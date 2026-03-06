use ark_bn254::Bn254;
use ark_ec::pairing::Pairing;
use ark_ff::Field;
use ark_relations::{
    lc,
    r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
        Result as R1CSResult, SynthesisError, Variable,
    },
};
use ark_std::rand::{SeedableRng, rngs::StdRng};

use curg_groth16_research::{
    Circuit, constraint_matrices_to_dense_matrices, prove::prove, setup::setup, verify::verify,
};


// in >= 10 을 증명하는 서킷
// 제약 전략: in = d + 10 (d >= 0) 을 비트 분해로 강제
#[derive(Clone)]
struct GreaterThanTenCircuit<F: Field> {
    // Private witness (검증자에게 비공개)
    pub in_: Option<F>,
    // Private witnesses
    pub d:   Option<F>,
    pub d0:  Option<F>,  // d의 비트 0 (2⁰)
    pub d1:  Option<F>,  // d의 비트 1 (2¹)
    pub d2:  Option<F>,  // d의 비트 2 (2²)
    pub d3:  Option<F>,  // d의 비트 3 (2³)
    pub in0: Option<F>,  // in의 비트 0 (2⁰)
    pub in1: Option<F>,  // in의 비트 1 (2¹)
    pub in2: Option<F>,  // in의 비트 2 (2²)
    pub in3: Option<F>,  // in의 비트 3 (2³)
}

impl<F: Field> ConstraintSynthesizer<F> for GreaterThanTenCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> R1CSResult<()> {
        // ── 변수 할당 ──────────────────────────────────────────────────────────
        let in_ = cs.new_witness_variable(|| self.in_.ok_or(SynthesisError::AssignmentMissing))?;

        let d  = cs.new_witness_variable(|| self.d.ok_or(SynthesisError::AssignmentMissing))?;
        let d0 = cs.new_witness_variable(|| self.d0.ok_or(SynthesisError::AssignmentMissing))?;
        let d1 = cs.new_witness_variable(|| self.d1.ok_or(SynthesisError::AssignmentMissing))?;
        let d2 = cs.new_witness_variable(|| self.d2.ok_or(SynthesisError::AssignmentMissing))?;
        let d3 = cs.new_witness_variable(|| self.d3.ok_or(SynthesisError::AssignmentMissing))?;

        let in0 = cs.new_witness_variable(|| self.in0.ok_or(SynthesisError::AssignmentMissing))?;
        let in1 = cs.new_witness_variable(|| self.in1.ok_or(SynthesisError::AssignmentMissing))?;
        let in2 = cs.new_witness_variable(|| self.in2.ok_or(SynthesisError::AssignmentMissing))?;
        let in3 = cs.new_witness_variable(|| self.in3.ok_or(SynthesisError::AssignmentMissing))?;

        // ── 제약 1: in = d + 10  →  (d + 10) × 1 = in ────────────────────────
        cs.enforce_constraint(
            lc!() + d + (F::from(10u64), Variable::One),
            lc!() + Variable::One,
            lc!() + in_,
        )?;

        // ── 제약 2: d = d0·2⁰ + d1·2¹ + d2·2² + d3·2³ ──────────────────────
        cs.enforce_constraint(
            lc!() + d0 + (F::from(2u64), d1) + (F::from(4u64), d2) + (F::from(8u64), d3),
            lc!() + Variable::One,
            lc!() + d,
        )?;

        // ── 제약 3~6: d_i ∈ {0,1}  →  d_i × (d_i - 1) = 0 ──────────────────
        cs.enforce_constraint(lc!() + d0, lc!() + d0 + (-F::from(1u64), Variable::One), lc!())?;
        cs.enforce_constraint(lc!() + d1, lc!() + d1 + (-F::from(1u64), Variable::One), lc!())?;
        cs.enforce_constraint(lc!() + d2, lc!() + d2 + (-F::from(1u64), Variable::One), lc!())?;
        cs.enforce_constraint(lc!() + d3, lc!() + d3 + (-F::from(1u64), Variable::One), lc!())?;

        // ── 제약 7: in = in0·2⁰ + in1·2¹ + in2·2² + in3·2³ ─────────────────
        cs.enforce_constraint(
            lc!() + in0 + (F::from(2u64), in1) + (F::from(4u64), in2) + (F::from(8u64), in3),
            lc!() + Variable::One,
            lc!() + in_,
        )?;

        // ── 제약 8~11: in_i ∈ {0,1}  →  in_i × (in_i - 1) = 0 ──────────────
        cs.enforce_constraint(lc!() + in0, lc!() + in0 + (-F::from(1u64), Variable::One), lc!())?;
        cs.enforce_constraint(lc!() + in1, lc!() + in1 + (-F::from(1u64), Variable::One), lc!())?;
        cs.enforce_constraint(lc!() + in2, lc!() + in2 + (-F::from(1u64), Variable::One), lc!())?;
        cs.enforce_constraint(lc!() + in3, lc!() + in3 + (-F::from(1u64), Variable::One), lc!())?;

        Ok(())
    }
}

fn main() {
    type P = Bn254;
    type ScalarField = <P as Pairing>::ScalarField;

    // in = 13 > 10  →  d = in - 10 = 3
    // in = 13 = 1101₂  →  in0=1, in1=0, in2=1, in3=1  (1 + 0 + 4 + 8 = 13)
    // d  =  3 = 0011₂  →  d0=1,  d1=1,  d2=0,  d3=0  (1 + 2 + 0 + 0 = 3)
    let c = GreaterThanTenCircuit {
        in_: Some(ScalarField::from(13u64)),
        d:   Some(ScalarField::from(3u64)),
        d0:  Some(ScalarField::from(1u64)),
        d1:  Some(ScalarField::from(1u64)),
        d2:  Some(ScalarField::from(0u64)),
        d3:  Some(ScalarField::from(0u64)),
        in0: Some(ScalarField::from(1u64)),
        in1: Some(ScalarField::from(0u64)),
        in2: Some(ScalarField::from(1u64)),
        in3: Some(ScalarField::from(1u64)),
    };


    let cs = ConstraintSystem::<ScalarField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::None);
    c.generate_constraints(cs.clone()).unwrap();
    cs.finalize();

    // witness 값들이 모든 R1CS constraint를 만족하는지 검증하는 sanity check.
    // 각 constraint(A·z ∘ B·z = C·z)에 실제 변수 값을 대입해 성립 여부를 확인한다.
    // 잘못된 witness(예: x=3인데 y=25)로 proof를 생성하면 수학적으로 불가능하므로,
    // proof 생성 전에 미리 오류를 잡아낸다.
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