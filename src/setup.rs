use ark_ec::{CurveGroup, PrimeGroup, pairing::Pairing};
use ark_ff::Field;
use ark_poly::Polynomial;
use ark_std::{UniformRand, rand::Rng};

use crate::Circuit;

#[derive(Clone, Debug, PartialEq)]
#[allow(clippy::upper_case_acronyms)]
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

fn generate_powers_of_tau<F, G>(g: G, tau: F, n: usize) -> Vec<G::Affine>
where
    F: Field,
    G: CurveGroup<ScalarField = F>,
{
    (0..n)
        .map(|i| tau.pow([i as u64]))
        .map(|x| (g * x).into())
        .collect()
}

pub fn setup<E: Pairing>(rng: &mut impl Rng, circuit: &Circuit<E>) -> SRS<E> {
    let g1_generator = E::G1::generator();
    let g2_generator = E::G2::generator();

    let alpha = E::ScalarField::rand(rng);
    let beta = E::ScalarField::rand(rng);
    let tau = E::ScalarField::rand(rng);
    let gamma = E::ScalarField::rand(rng);
    let delta = E::ScalarField::rand(rng);

    let powers_of_tau_g1 = generate_powers_of_tau(g1_generator, tau, circuit.num_constraints());
    let powers_of_tau_g2 = generate_powers_of_tau(g2_generator, tau, circuit.num_constraints());

    let t_at_tau = circuit.t().evaluate(&tau);
    let upsilons_g1 = (0..circuit.num_constraints() - 1)
        .map(|i| tau.pow([i as u64]))
        .map(|power_of_tau| (g1_generator * (power_of_tau * t_at_tau / delta)).into())
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
        .map(|x| (g1_generator * x).into())
        .collect();

    SRS {
        alpha_g1: (g1_generator * alpha).into(),
        beta_g1: (g1_generator * beta).into(),
        beta_g2: (g2_generator * beta).into(),
        gamma_g2: (g2_generator * gamma).into(),
        delta_g1: (g1_generator * delta).into(),
        delta_g2: (g2_generator * delta).into(),
        powers_of_tau_g1,
        powers_of_tau_g2,
        upsilons_g1,
        psis_g1: psis,
    }
}
