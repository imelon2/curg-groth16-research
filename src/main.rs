use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ff::Field;
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use ark_relations::{
    lc,
    r1cs::{
        ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
        OptimizationGoal, Result as R1CSResult, SynthesisError,
    },
};
use ark_std::rand::{SeedableRng, rngs::StdRng};

mod polynomial;
mod prove;
mod setup;
mod verify;

use crate::{polynomial::lagrange_interpolate, prove::prove, setup::setup, verify::verify};

#[derive(Clone, Debug, PartialEq)]
pub struct Circuit<E: Pairing> {
    // R1CS matrices
    pub l: Vec<Vec<E::ScalarField>>,
    pub r: Vec<Vec<E::ScalarField>>,
    pub o: Vec<Vec<E::ScalarField>>,

    pub num_public_inputs: usize,
    pub num_private_inputs: usize,
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

    fn matrix_to_qap<F: Field>(m: &[Vec<F>]) -> Vec<DensePolynomial<F>> {
        let xs: Vec<F> = (1..=m.len() as u64).map(F::from).collect();
        (0..m[0].len())
            .map(|c| m.iter().map(|r| r[c]).collect())
            .map(|ys: Vec<F>| lagrange_interpolate(&xs, &ys))
            .collect()
    }

    pub fn r1cs_to_qap(
        &self,
    ) -> (
        Vec<DensePolynomial<E::ScalarField>>, // u_polys
        Vec<DensePolynomial<E::ScalarField>>, // v_polys
        Vec<DensePolynomial<E::ScalarField>>, // w_polys
    ) {
        (
            Self::matrix_to_qap(&self.l),
            Self::matrix_to_qap(&self.r),
            Self::matrix_to_qap(&self.o),
        )
    }
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
    let public_inputs = binding.instance_assignment.clone();
    let private_inputs = binding.witness_assignment.clone();
    println!("public_inputs: {:?}", public_inputs);
    println!("private_inputs: {:?}", private_inputs);
    println!("witness: {:?}", a);

    let circuit: Circuit<P> = Circuit {
        l,
        r,
        o,
        num_public_inputs: cs.num_instance_variables(),
        num_private_inputs: cs.num_witness_variables(),
    };

    let rng = &mut StdRng::seed_from_u64(0);

    let srs = setup::<P>(rng, &circuit);

    let proof = prove::<P>(rng, &circuit, &srs, &a);
    println!("proof: {:?}", &proof);

    println!(
        "verified: {}",
        verify::<P>(&circuit, &srs, &public_inputs, &proof)
    );
}
