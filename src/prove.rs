use ark_ec::{CurveGroup, pairing::Pairing};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_std::{UniformRand, rand::Rng};

use crate::{Circuit, setup::SRS};

#[derive(Clone, Debug, PartialEq)]
pub struct Proof<E: Pairing> {
    pub a_g1: E::G1Affine,
    pub b_g2: E::G2Affine,
    pub c_g1: E::G1Affine,
}

fn inner_product_polys_with_witness<F: Field>(
    polys: &[DensePolynomial<F>],
    a: &[F],
) -> DensePolynomial<F> {
    polys
        .iter()
        .zip(a)
        .map(|(ui, &ai)| ui * ai)
        .reduce(|a, b| a + b)
        .unwrap()
}

fn inner_product_poly_coeffs_with_powers_of_tau<F: Field, G: CurveGroup<ScalarField = F>>(
    coeffs: &[F],
    powers_of_tau: &[G::Affine],
) -> G {
    coeffs
        .iter()
        .zip(powers_of_tau)
        .map(|(a_u, &power_of_tau)| power_of_tau * a_u)
        .sum::<G>()
}

pub fn prove<E: Pairing>(
    rng: &mut impl Rng,
    circuit: &Circuit<E>,
    srs: &SRS<E>,
    a: &[E::ScalarField],
) -> Proof<E> {
    let (u_polys, v_polys, w_polys) = circuit.r1cs_to_qap();
    let sum_a_u = inner_product_polys_with_witness(&u_polys, a);
    let sum_a_v = inner_product_polys_with_witness(&v_polys, a);
    let sum_a_w = inner_product_polys_with_witness(&w_polys, a);

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

    let sum_a_u_at_tau_g1: E::G1 =
        inner_product_poly_coeffs_with_powers_of_tau(&sum_a_u.coeffs, &srs.powers_of_tau_g1);
    let sum_a_v_at_tau_g1: E::G1 =
        inner_product_poly_coeffs_with_powers_of_tau(&sum_a_v.coeffs, &srs.powers_of_tau_g1);
    let sum_a_v_at_tau_g2: E::G2 =
        inner_product_poly_coeffs_with_powers_of_tau(&sum_a_v.coeffs, &srs.powers_of_tau_g2);

    let r = E::ScalarField::rand(rng);
    let s = E::ScalarField::rand(rng);

    let a_g1: E::G1 = srs.alpha_g1 + sum_a_u_at_tau_g1 + srs.delta_g1 * r;
    let b_g1: E::G1 = srs.beta_g1 + sum_a_v_at_tau_g1 + srs.delta_g1 * s;
    let b_g2: E::G2 = srs.beta_g2 + sum_a_v_at_tau_g2 + srs.delta_g2 * s;

    let sum_a_psi_for_private_inputs: E::G1 = (circuit.num_public_inputs..circuit.num_inputs())
        .map(|i| srs.psis_g1[i] * a[i])
        .sum();
    let c_g1: E::G1 =
        sum_a_psi_for_private_inputs + h_t_at_tau + a_g1 * s + b_g1 * r - srs.delta_g1 * r * s;

    Proof {
        a_g1: a_g1.into_affine(),
        b_g2: b_g2.into_affine(),
        c_g1: c_g1.into_affine(),
    }
}
