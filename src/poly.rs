pub use crate::matrix::Matrix;
pub use anyhow::anyhow;
use ff::{Field, PrimeField};
use std::convert::TryFrom;
use std::{
  cmp::max,
  fmt::{Display, Formatter},
  ops::{Add, AddAssign, Div, Mul, MulAssign, Sub, SubAssign}
};

#[derive(Clone, Debug, PartialEq)]
pub struct Poly<F: Field>(Vec<F>);

impl<F: PrimeField> Poly<F> {
  pub fn new(coeffs: Vec<F>) -> Self {
    let mut poly = Poly(coeffs);
    poly.normalize();
    poly
  }

  pub fn from(coeffs: &[i64]) -> Self {
    Poly::new(coeffs.iter().map(|n| {
      if *n > 0 {
        F::from(*n as u64)
      }
      else {
        -F::from(-*n as u64)
      } 
    }).collect::<Vec<F>>())
  }

  pub fn coeffs(&self) -> &[F] {
    &self.0
  }

  pub fn into_coeffs(self) -> Vec<F> {
    self.0
  }

  pub fn zero() -> Self {
    Poly(vec![F::zero()])
  }

  pub fn one() -> Self {
    Poly(vec![F::one()])
  }

  pub fn lagrange(p: &[(F, F)]) -> Self {
    let k = p.len();
    let mut l = Poly::zero();
    for j in 0..k {
      let mut l_j = Poly::one();
      for i in 0..k {
        if i != j {
          let c = (p[j].0 - p[i].0).invert();
          assert!(bool::from(c.is_some()), "lagrange polinomial x points must be unique");
          let c = c.unwrap();
          l_j = &l_j * &Poly::new(vec![-(c * p[i].0), c]);
        }
      }
      l += &(&l_j * p[j].1);
    }
    l
  }

  pub fn z(points: &[F]) -> Self {
    points
      .iter()
      .fold(Poly::one(), |acc, x| &acc * &Poly::new(vec![-*x, F::one()]))
  }

  pub fn eval(&self, x: &F) -> F {
    let mut x_pow = F::one();
    let mut y = self.0[0];
    for (i, _) in self.0.iter().enumerate().skip(1) {
      x_pow *= x;
      y += self.0[i] * x_pow;
    }
    y
  }

  pub fn eval_with_pows(&self, x_pow: &[F]) -> F {
    let mut y = self.0[0];
    for (i, _) in self.0.iter().enumerate().skip(1) {
      y += self.0[i] * x_pow[i];
    }
    y
  }

  pub fn degree(&self) -> usize {
    self.0.len() - 1
  }

  pub fn normalize(&mut self) {
    if self.0.len() > 1 && bool::from(self.0[self.0.len()-1].is_zero()) {
      let first_none_zero = self.0.iter().rev().position(|p| !bool::from(p.is_zero()));
      if let Some(first_none_zero) = first_none_zero {
        self.0.resize(self.0.len() - first_none_zero, F::zero());
      } else {
        self.0.resize(1, F::zero());
      }
    }
  }

  pub fn is_zero(&self) -> bool {
    self.0.len() == 1 && bool::from(self.0[0].is_zero())
  }

  pub fn set(&mut self, i: usize, p: F) {
    if self.0.len() < i+1 {
      self.0.resize(i+1, F::zero());
    }
    self.0[i] = p;
    self.normalize();
  }

  pub fn get(&self, i: usize) -> Option<&F> {
    self.0.get(i)
  }

}

impl<F: PrimeField> Display for Poly<F> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
      let mut first: bool = true;
      for i in 0..=self.degree() {
          if bool::from(self.0[i].is_zero()) && self.degree() > 1 {
              continue;
          }
          let v = format!("{:?}", self.0[i]);
          if !first {
              write!(f, "+")?;
          }
          if i == 0 || v != "1" {
              write!(f, "{}", v)?;
          }
          if i >= 1 {
              write!(f, "x")?;
          }
          if i >= 2 {
              write!(f, "^{}", i)?;
          }
          first = false;
      }
      Ok(())
  }
}

impl<F: PrimeField> TryFrom<Matrix<F>> for Poly<F> {
  type Error = anyhow::Error;
  fn try_from(matrix: Matrix<F>) -> Result<Self, Self::Error> {
      if matrix.cols() == 1 {
          Ok(Poly::new(matrix.into()))
      } else {
          Err(anyhow!("only one row"))
      }
  }
}

impl<F: PrimeField> AddAssign<&Poly<F>> for Poly<F> {
  fn add_assign(&mut self, rhs: &Poly<F>) {
      for n in 0..max(self.0.len(), rhs.0.len()) {
          if n >= self.0.len() {
              self.0.push(rhs.0[n]);
          } else if n < self.0.len() && n < rhs.0.len() {
              self.0[n] += rhs.0[n];
          }
      }
      self.normalize();
  }
}


impl<F: PrimeField> AddAssign<&F> for Poly<F> {
  fn add_assign(&mut self, rhs: &F) {
      self.0[0] += rhs;
      self.normalize();
  }
}

impl<F: PrimeField> SubAssign<&F> for Poly<F> {
  fn sub_assign(&mut self, rhs: &F) {
      self.0[0] -= rhs;
      self.normalize();
  }
}

impl<F: PrimeField> SubAssign<&Poly<F>> for Poly<F> {
  fn sub_assign(&mut self, rhs: &Poly<F>) {
      for n in 0..max(self.0.len(), rhs.0.len()) {
          if n >= self.0.len() {
              self.0.push(rhs.0[n]);
          } else if n < self.0.len() && n < rhs.0.len() {
              self.0[n] -= &rhs.0[n];
          }
      }
      self.normalize();
  }
}


impl<F: PrimeField> Mul<&Poly<F>> for &Poly<F> {
  type Output = Poly<F>;
  fn mul(self, rhs: &Poly<F>) -> Self::Output {
      let mut mul = vec![F::zero(); self.0.len() + rhs.0.len()];
      for n in 0..self.0.len() {
          for m in 0..rhs.0.len() {
              mul[n + m] += self.0[n] * rhs.0[m];
          }
      }
      let mut m = Poly(mul);
      m.normalize();
      m
  }
}

impl<F: PrimeField> MulAssign<&F> for Poly<F> {
  fn mul_assign(&mut self, rhs: &F) {
      if bool::from(rhs.is_zero()) {
          *self = Poly::zero()
      } else {
          self.0.iter_mut().for_each(|v| *v = *v * rhs);
      }
  }
}

impl<F: PrimeField> Div for Poly<F> {
  type Output = (Poly<F>, Poly<F>);

  fn div(self, rhs: Poly<F>) -> Self::Output {
      let (mut q, mut r) = (Poly::zero(), self);
      while !r.is_zero() && r.degree() >= rhs.degree() {
          let lead_r = r.0[r.0.len() - 1];
          let lead_d = rhs.0[rhs.0.len() - 1];
          let mut t = Poly::zero();
          t.set(r.0.len() - rhs.0.len(), lead_r * lead_d.invert().unwrap());
          q += &t;
          r -= &(&rhs * &t);
      }
      q.normalize();
      r.normalize();
      (q, r)
  }
}

impl<F: PrimeField> Add for Poly<F> {
  type Output = Poly<F>;
  fn add(mut self, rhs: Poly<F>) -> Self::Output {
      self += &rhs;
      self
  }
}

impl<F: PrimeField> Add<Poly<F>> for &Poly<F> {
  type Output = Poly<F>;
  fn add(self, rhs: Poly<F>) -> Self::Output {
      let mut v = self.clone();
      v += &rhs;
      v
  }
}

impl<F: PrimeField> Add<&Poly<F>> for Poly<F> {
  type Output = Poly<F>;
  fn add(mut self, rhs: &Poly<F>) -> Self::Output {
      self += rhs;
      self
  }
}

impl<F: PrimeField> Add<&Poly<F>> for &Poly<F> {
  type Output = Poly<F>;
  fn add(self, rhs: &Poly<F>) -> Self::Output {
      let mut v = self.clone();
      v += rhs;
      v
  }
}

impl<F: PrimeField> Add<&F> for Poly<F> {
  type Output = Poly<F>;
  fn add(mut self, rhs: &F) -> Self::Output {
      self += rhs;
      self
  }
}

impl<F: PrimeField> Add<F> for Poly<F> {
  type Output = Poly<F>;
  fn add(mut self, rhs: F) -> Self::Output {
      self += &rhs;
      self
  }
}

impl<F: PrimeField> Sub<F> for Poly<F> {
  type Output = Poly<F>;
  fn sub(mut self, rhs: F) -> Self::Output {
      self -= &rhs;
      self
  }
}

impl<F: PrimeField> Add<F> for &Poly<F> {
  type Output = Poly<F>;
  fn add(self, rhs: F) -> Self::Output {
      let mut cloned = self.clone();
      cloned += &rhs;
      cloned
  }
}

impl<F: PrimeField> Sub<Poly<F>> for Poly<F> {
  type Output = Poly<F>;
  fn sub(mut self, rhs: Poly<F>) -> Self::Output {
      self -= &rhs;
      self
  }
}

impl<F: PrimeField> Mul<&Poly<F>> for Poly<F> {
  type Output = Poly<F>;
  fn mul(self, rhs: &Poly<F>) -> Self::Output {
      &self * rhs
  }
}

impl<F: PrimeField> Mul<Poly<F>> for &Poly<F> {
  type Output = Poly<F>;
  fn mul(self, rhs: Poly<F>) -> Self::Output {
      self * &rhs
  }
}

impl<F: PrimeField> Mul<Poly<F>> for Poly<F> {
  type Output = Poly<F>;
  fn mul(self, rhs: Poly<F>) -> Self::Output {
      self * &rhs
  }
}

impl<F: PrimeField> Mul<&F> for &Poly<F> {
  type Output = Poly<F>;
  fn mul(self, rhs: &F) -> Self::Output {
      let mut m = self.clone();
      m *= rhs;
      m
  }
}

impl<F: PrimeField> Mul<&F> for Poly<F> {
  type Output = Poly<F>;
  fn mul(self, rhs: &F) -> Self::Output {
      &self * rhs
  }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Mul<F> for Poly<F> {
    type Output = Poly<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self * &rhs
    }
}

#[allow(clippy::op_ref)]
impl<F: PrimeField> Mul<F> for &Poly<F> {
    type Output = Poly<F>;
    fn mul(self, rhs: F) -> Self::Output {
        self * &rhs
    }
}

struct PolyFreq<F: PrimeField>(Vec<F>);
impl<F: PrimeField> Mul for PolyFreq<F> {
  type Output = PolyFreq<F>;
  fn mul(self, rhs: PolyFreq<F>) -> Self::Output {
    let zero = F::zero();
    let mut c_freq = Vec::new();
    for n in 0..self.0.len() {
      let l = self.0.get(n).unwrap_or(&zero);
      let r = rhs.0.get(n).unwrap_or(&zero);
      c_freq.push(*l * r);
    }
    Self(c_freq)
  }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bls12_381::Scalar as F;
    type P = Poly<F>;

    #[test]
    fn test_poly_add() {
        let mut p246 = P::from(&[1, 2, 3]);
        p246 += &P::from(&[1, 2, 3]);
        assert_eq!(p246, P::from(&[2, 4, 6]));

        let mut p24645 = P::from(&[1, 2, 3]);
        p24645 += &P::from(&[1, 2, 3, 4, 5]);
        assert_eq!(p24645, P::from(&[2, 4, 6, 4, 5]));

        let mut p24646 = P::from(&[1, 2, 3, 4, 6]);
        p24646 += &P::from(&[1, 2, 3]);
        assert_eq!(p24646, Poly::from(&[2, 4, 6, 4, 6]));
    }

    #[test]
    fn test_poly_sub() {
        let mut p0 = P::from(&[1, 2, 3]);
        p0 -= &P::from(&[1, 2, 3]);
        assert_eq!(p0, P::from(&[0]));

        let mut p003 = P::from(&[1, 2, 3]);
        p003 -= &P::from(&[1, 2]);
        assert_eq!(p003, P::from(&[0, 0, 3]));
    }

    #[test]
    fn test_poly_mul() {
        assert_eq!(
            &P::from(&[5, 0, 10, 6]) * &P::from(&[1, 2, 4]),
            P::from(&[5, 10, 30, 26, 52, 24])
        );
    }

    #[test]
    fn test_poly_div() {
        fn do_test(n: P, d: P) {
            let (q, r) = n.clone() / d.clone();
            let mut n2 = &q * &d;
            n2 += &r;
            assert_eq!(n, n2);
        }

        do_test(P::from(&[1]), P::from(&[1, 1]));
        do_test(P::from(&[1, 1]), P::from(&[1, 1]));
        do_test(P::from(&[1, 2, 1]), P::from(&[1, 1]));
        do_test(P::from(&[1, 2, 1, 2, 5, 8, 1, 9]), P::from(&[1, 1, 5, 4]));
    }

    #[test]
    fn test_poly_print() {
        assert_eq!("1+2x+x^2", format!("{}", P::from(&[1, 2, 1])));
        assert_eq!("1+x^2", format!("{}", P::from(&[1, 0, 1])));
        assert_eq!("x^2", format!("{}", P::from(&[0, 0, 1])));
        assert_eq!("2x^2", format!("{}", P::from(&[0, 0, 2])));
    }

    #[test]
    fn test_poly_lagrange_multi() {
        let points = vec![
            (F::from(1u64), F::from(2u64)),
            (F::from(5u64), F::from(7u64)),
            (F::from(7u64), F::from(9u64)),
            (F::from(3u64), F::from(1u64)),
        ];
        let l = Poly::lagrange(&points);
        points.iter().for_each(|p| assert_eq!(l.eval(&p.0), p.1));
    }
    #[test]
    fn test_poly_z() {
        assert_eq!(
            P::z(&vec![F::from(1u64), F::from(5u64)]),
            P::from(&[5, -6, 1]) // f(x) = (x-1)(x-5) = x^2-6x+5
        );
    }
    #[test]
    fn test_poly_eval() {
        // check that (x^2+2x+1)(2) = 9
        assert_eq!(P::from(&[1, 2, 1]).eval(&F::from(2u64)), F::from(9u64));
    }
    #[test]
    fn test_poly_normalize() {
        let mut p1 = P::from(&[1, 0, 0, 0]);
        p1.normalize();
        assert_eq!(p1, P::from(&[1]));
    }
}