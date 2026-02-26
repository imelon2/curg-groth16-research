use ark_bn254::Bn254;
use ark_ec::{CurveGroup, PrimeGroup, pairing::Pairing};
use ark_ff::{Field, Zero};
use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
use ark_relations::{
    lc,
    r1cs::{
        ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
        OptimizationGoal, Result as R1CSResult, SynthesisError,
    },
};
use ark_std::{
    UniformRand,
    rand::{Rng, SeedableRng, rngs::StdRng},
};

fn poly_scale<F: Field>(p: &DensePolynomial<F>, k: F) -> DensePolynomial<F> {
    DensePolynomial::from_coefficients_vec(p.coeffs().iter().map(|c| *c * k).collect())
}

fn lagrange_interpolate<F: Field>(xs: &[F], ys: &[F]) -> DensePolynomial<F> {
    assert_eq!(xs.len(), ys.len());
    assert!(!xs.is_empty());

    let n = xs.len();
    let mut f = DensePolynomial::zero();

    for i in 0..n {
        let mut basis = DensePolynomial::from_coefficients_slice(&[F::from(1)]);
        let mut denom = F::one();

        for j in 0..n {
            if i == j {
                continue;
            }
            basis = basis.naive_mul(&DensePolynomial::from_coefficients_slice(&[
                -xs[j],
                F::one(),
            ]));
            denom *= xs[i] - xs[j];
        }

        let li = poly_scale(&basis, denom.inverse().unwrap());
        let term = poly_scale(&li, ys[i]);
        f = &f + &term;
    }

    f
}

#[derive(Clone, Debug, PartialEq)]
pub struct Circuit<E: Pairing> {
    // R1CS matrices
    pub l: Vec<Vec<E::ScalarField>>,
    pub r: Vec<Vec<E::ScalarField>>,
    pub o: Vec<Vec<E::ScalarField>>,

    pub num_public_inputs: usize,
    pub num_private_inputs: usize,
}

#[derive(Clone)]
struct MyCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

impl<F: Field> ConstraintSynthesizer<F> for MyCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> R1CSResult<()> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
            a *= &b;
            Ok(a)
        })?;

        cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        Ok(())
    }
}

impl<E: Pairing> Circuit<E> {
    pub fn num_constraints(&self) -> usize {
        assert!(self.l.len() == self.r.len() && self.r.len() == self.o.len());
        self.l.len()
    }

    pub fn num_inputs(&self) -> usize {
        self.num_public_inputs + self.num_private_inputs
    }

    pub fn t(&self) -> DensePolynomial<E::ScalarField> {
        (1..=self.num_constraints())
            .map(|i| {
                // (x - i) term
                DensePolynomial::from_coefficients_slice(&[
                    -E::ScalarField::from(i as u64),
                    E::ScalarField::ONE,
                ])
            })
            .reduce(|a, b| a * b) // product
            .unwrap()
    }

    pub fn r1cs_to_qap(
        &self,
    ) -> (
        Vec<DensePolynomial<E::ScalarField>>, // u_polys
        Vec<DensePolynomial<E::ScalarField>>, // v_polys
        Vec<DensePolynomial<E::ScalarField>>, // w_polys
    ) {
        let xs: Vec<E::ScalarField> = (1..=self.l.len() as u8).map(E::ScalarField::from).collect();
        let u_polys: Vec<DensePolynomial<E::ScalarField>> = (0..self.l[0].len())
            .map(|c| self.l.iter().map(|r| r[c]).collect())
            .map(|ys: Vec<E::ScalarField>| lagrange_interpolate(&xs, &ys))
            .collect();
        let v_polys: Vec<DensePolynomial<E::ScalarField>> = (0..self.r[0].len())
            .map(|c| self.r.iter().map(|r| r[c]).collect())
            .map(|ys: Vec<E::ScalarField>| lagrange_interpolate(&xs, &ys))
            .collect();
        let w_polys: Vec<DensePolynomial<E::ScalarField>> = (0..self.o[0].len())
            .map(|c| self.o.iter().map(|r| r[c]).collect())
            .map(|ys: Vec<E::ScalarField>| lagrange_interpolate(&xs, &ys))
            .collect();

        (u_polys, v_polys, w_polys)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct SRS<E: Pairing> {
    pub alpha_g1: E::G1Affine,
    pub beta_g1: E::G1Affine,
    pub beta_g2: E::G2Affine,
    pub gamma_g2: E::G2Affine,
    pub delta_g1: E::G1Affine,
    pub delta_g2: E::G2Affine,

    pub powers_of_tau_g1: Vec<E::G1Affine>,
    pub powers_of_tau_g2: Vec<E::G2Affine>,
    pub upsilons_g1: Vec<E::G1Affine>,
    pub psis_g1: Vec<E::G1Affine>,
}

fn setup<E: Pairing>(rng: &mut impl Rng, circuit: &Circuit<E>) -> SRS<E> {
    let g1_generator = E::G1::generator();
    let g2_generator = E::G2::generator();

    let alpha = E::ScalarField::rand(rng);
    let beta = E::ScalarField::rand(rng);
    let tau = E::ScalarField::rand(rng);
    let gamma = E::ScalarField::rand(rng);
    let delta = E::ScalarField::rand(rng);

    let powers_of_tau_g1 = (0..circuit.num_constraints())
        .map(|i| tau.pow([i as u64])) // TODO: what if i exceeds u64?
        .map(|x| (g1_generator * x).into_affine())
        .collect();
    let powers_of_tau_g2 = (0..circuit.num_constraints())
        .map(|i| tau.pow([i as u64]))
        .map(|x| (g2_generator * x).into_affine())
        .collect();

    let t_at_tau = circuit.t().evaluate(&tau);
    let upsilons_g1 = (0..circuit.num_constraints() - 1)
        .map(|i| tau.pow([i as u64]))
        .map(|power_of_tau| (g1_generator * (power_of_tau * t_at_tau / delta)).into_affine())
        .collect();

    let (u_polys, v_polys, w_polys) = circuit.r1cs_to_qap();
    let psi_polys_at_tau = (0..circuit.num_inputs()).map(|i| {
        (v_polys[i].evaluate(&tau) * alpha)
            + (u_polys[i].evaluate(&tau) * beta)
            + w_polys[i].evaluate(&tau)
    });
    let psis = psi_polys_at_tau
        .enumerate()
        .map(|(i, x)| {
            if i < circuit.num_public_inputs {
                x / gamma
            } else {
                x / delta
            }
        })
        .map(|x| (g1_generator * x).into_affine())
        .collect();

    SRS {
        alpha_g1: (g1_generator * &alpha).into_affine(),
        beta_g1: (g1_generator * &beta).into_affine(),
        beta_g2: (g2_generator * &beta).into_affine(),
        gamma_g2: (g2_generator * &gamma).into_affine(),
        delta_g1: (g1_generator * &delta).into_affine(),
        delta_g2: (g2_generator * &delta).into_affine(),
        powers_of_tau_g1,
        powers_of_tau_g2,
        upsilons_g1,
        psis_g1: psis,
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Proof<E: Pairing> {
    pub a_g1: E::G1Affine,
    pub b_g2: E::G2Affine,
    pub c_g1: E::G1Affine,
}

fn prove<E: Pairing>(
    rng: &mut impl Rng,
    circuit: &Circuit<E>,
    srs: &SRS<E>,
    public_inputs: &[E::ScalarField],
    private_inputs: &[E::ScalarField],
) -> Proof<E> {
    let a = [public_inputs, private_inputs].concat();

    let (u_polys, v_polys, w_polys) = circuit.r1cs_to_qap();
    let sum_a_u = u_polys
        .iter()
        .zip(&a)
        .map(|(ui, &ai)| ui * ai)
        .reduce(|a, b| a + b)
        .unwrap();
    let sum_a_v = v_polys
        .iter()
        .zip(&a)
        .map(|(vi, &ai)| vi * ai)
        .reduce(|a, b| a + b)
        .unwrap();
    let sum_a_w = w_polys
        .iter()
        .zip(&a)
        .map(|(wi, &ai)| wi * ai)
        .reduce(|a, b| a + b)
        .unwrap();

    let h = (&sum_a_u * &sum_a_v - &sum_a_w) / circuit.t();

    // QAP verification
    // TODO: remove
    let temp_h_t = &h * circuit.t();
    assert_eq!(&sum_a_u * &sum_a_v, &sum_a_w + temp_h_t);

    let h_t_at_tau = srs
        .upsilons_g1
        .iter()
        .zip(&h.coeffs)
        .map(|(&a, b)| a * b)
        .sum::<E::G1>();

    let sum_a_u_at_tau_g1 = sum_a_u
        .iter()
        .zip(&srs.powers_of_tau_g1)
        .map(|(a_u, &power_of_tau)| power_of_tau * a_u)
        .sum::<E::G1>();
    let sum_a_v_at_tau_g1 = sum_a_v
        .iter()
        .zip(&srs.powers_of_tau_g1)
        .map(|(a_v, &power_of_tau)| power_of_tau * a_v)
        .sum::<E::G1>();
    let sum_a_v_at_tau_g2 = sum_a_v
        .iter()
        .zip(&srs.powers_of_tau_g2)
        .map(|(a_v, &power_of_tau)| power_of_tau * a_v)
        .sum::<E::G2>();

    let r = E::ScalarField::rand(rng);
    let s = E::ScalarField::rand(rng);

    let a_g1 = srs.alpha_g1 + sum_a_u_at_tau_g1 + srs.delta_g1 * r;
    let b_g1 = srs.beta_g1 + sum_a_v_at_tau_g1 + srs.delta_g1 * s;
    let b_g2 = srs.beta_g2 + sum_a_v_at_tau_g2 + srs.delta_g2 * s;

    let sum_a_psi_for_private_inputs = (circuit.num_public_inputs..circuit.num_inputs())
        .map(|i| srs.psis_g1[i] * a[i])
        .sum::<E::G1>();
    let c_g1 =
        sum_a_psi_for_private_inputs + h_t_at_tau + a_g1 * s + b_g1 * r - srs.delta_g1 * r * s;

    Proof {
        a_g1: a_g1.into_affine(),
        b_g2: b_g2.into_affine(),
        c_g1: c_g1.into_affine(),
    }
}

fn verify<E: Pairing>(
    circuit: &Circuit<E>,
    srs: &SRS<E>,
    public_inputs: &[E::ScalarField],
    proof: &Proof<E>,
) -> bool {
    assert_eq!(public_inputs.len(), circuit.num_public_inputs);

    let x_g1 = srs.psis_g1[..circuit.num_public_inputs]
        .iter()
        .zip(public_inputs)
        .map(|(&psi_i, public_input)| psi_i * public_input)
        .sum::<E::G1>();

    E::multi_pairing(
        [srs.alpha_g1, x_g1.into(), proof.c_g1],
        [srs.beta_g2, srs.gamma_g2, srs.delta_g2],
    )
    .0 == E::pairing(proof.a_g1, proof.b_g2).0
}

fn constraint_matrices_to_dense_matrices<F: Field>(
    cm: &ConstraintMatrices<F>,
) -> (Vec<Vec<F>>, Vec<Vec<F>>, Vec<Vec<F>>) {
    let mut dense_matrices =
        vec![
            vec![
                vec![F::zero(); cm.num_instance_variables + cm.num_witness_variables];
                cm.num_constraints
            ];
            3
        ];
    for (i, &sparse_matrix) in [&cm.a, &cm.b, &cm.c].iter().enumerate() {
        for (j, row) in sparse_matrix.iter().enumerate() {
            for elem in row {
                dense_matrices[i][j][elem.1] = elem.0;
            }
        }
    }
    (
        dense_matrices[0].clone(),
        dense_matrices[1].clone(),
        dense_matrices[2].clone(),
    )
}

fn main() {
    type P = Bn254;
    type ScalarField = <P as Pairing>::ScalarField;

    let c = MyCircuit {
        a: Some(ScalarField::from(5)),
        b: Some(ScalarField::from(7)),
    };

    let cs = ConstraintSystem::<ScalarField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::None);
    c.generate_constraints(cs.clone()).unwrap();
    cs.finalize();
    assert!(cs.is_satisfied().unwrap());

    let (l, r, o) = constraint_matrices_to_dense_matrices(&cs.to_matrices().unwrap());
    let binding = cs.borrow().unwrap();
    let a = [
        binding.instance_assignment.clone(),
        binding.witness_assignment.clone(),
    ]
    .concat();
    println!("num_instance_variables: {}", cs.num_instance_variables());
    println!("num_witness_variables: {}", cs.num_witness_variables());
    println!("{:?}", a);

    let circuit: Circuit<P> = Circuit {
        l,
        r,
        o,
        num_public_inputs: cs.num_instance_variables(),
        num_private_inputs: cs.num_witness_variables(),
    };

    // R1CS verification
    // TODO: remove
    let l_a: Vec<ScalarField> = circuit
        .l
        .iter()
        .map(|r| r.iter().zip(&a).map(|(&x, y)| x * y).sum())
        .collect();
    let r_a: Vec<ScalarField> = circuit
        .r
        .iter()
        .map(|r| r.iter().zip(&a).map(|(&x, y)| x * y).sum())
        .collect();
    let o_a: Vec<ScalarField> = circuit
        .o
        .iter()
        .map(|r| r.iter().zip(&a).map(|(&x, y)| x * y).sum())
        .collect();
    assert_eq!(
        l_a.iter()
            .zip(&r_a)
            .map(|(&a, b)| a * b)
            .collect::<Vec<ScalarField>>(),
        o_a
    );

    let public_inputs = &a[0..circuit.num_public_inputs];
    let private_inputs = &a[circuit.num_public_inputs..];
    println!("public_inputs: {:?}", public_inputs);
    println!("private_inputs: {:?}", private_inputs);

    let rng = &mut StdRng::seed_from_u64(0);
    let srs = setup::<P>(rng, &circuit);
    let proof = prove::<P>(rng, &circuit, &srs, &public_inputs, &private_inputs);
    println!("proof: {:?}", &proof);
    println!(
        "verified: {}",
        verify::<P>(&circuit, &srs, &public_inputs, &proof)
    );
}
