use ark_ff::{Field, Zero};
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};

fn poly_scale<F: Field>(p: &DensePolynomial<F>, k: F) -> DensePolynomial<F> {
    DensePolynomial::from_coefficients_vec(p.coeffs().iter().map(|c| *c * k).collect())
}

pub fn lagrange_interpolate<F: Field>(xs: &[F], ys: &[F]) -> DensePolynomial<F> {
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
