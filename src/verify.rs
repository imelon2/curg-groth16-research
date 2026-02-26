use ark_ec::pairing::Pairing;

use crate::{Circuit, prove::Proof, setup::SRS};

pub fn verify<E: Pairing>(
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
