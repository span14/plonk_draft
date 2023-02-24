
#![allow(clippy::many_single_char_names)]

use super::{
    constraints::*,
    matrix::Matrix,
    poly::Poly,
};

use bls12_381::{G1Projective as G1, G2Projective as G2, Scalar as Fq, pairing, G1Affine, G2Affine};
 
#[derive(PartialEq)]
pub struct PlonkTypes {
  pub K1: Fq,
  pub K2: Fq,
  pub OMEGA: Fq
}

#[derive(Debug)]
pub struct SRS {  
  pub g1s: Vec<G1>,
  pub g2_1: G2,
  pub g2_s: G2
}

impl SRS {
  pub fn create(s: Fq, n: usize) -> Self {
    let mut g1s = Vec::new();
    let mut s_pow = s;
    g1s.push(G1::generator());
    for _ in 0..n {
      g1s.push(G1::generator() * s_pow);
      s_pow = s_pow * s;
    }
    Self {
      g1s, 
      g2_1: G2::generator(),
      g2_s: G2::generator() * s,
    }
  }

  pub fn eval_at_s(&self, vs: &Poly<Fq>) -> G1 {
    vs.coeffs()
      .iter()
      .enumerate()
      .fold(G1::identity(), |acc, (n, v)| {
        acc + self.g1s[n] * v
      })
  }
}

#[derive(Debug, PartialEq)]
pub struct Proof {
  pub a_s: G1,
  pub b_s: G1,
  pub c_s: G1,
  pub z_s: G1,
  pub t_lo_s: G1,
  pub t_mid_s: G1,
  pub t_hi_s: G1,
  pub w_z_s: G1,
  pub w_z_omega_s: G1,
  pub a_z: Fq,
  pub b_z: Fq,
  pub c_z: Fq,
  pub s_sigma_1_z: Fq,
  pub s_sigma_2_z: Fq,
  pub z_omega_z: Fq,
}

pub struct Challenge {
  pub alpha: Fq,
  pub beta: Fq,
  pub gamma: Fq,
  pub z: Fq,
  pub v: Fq,
}

pub struct Plonk{
  srs: SRS,
  h: Vec<Fq>,
  h_pows_inv: Matrix<Fq>,
  k1_h: Vec<Fq>,
  k2_h: Vec<Fq>,
  z_h_x: Poly<Fq>,
}

impl Plonk {
  pub fn new(srs: SRS, omega_pows: u64, P: &PlonkTypes) -> Self {
    let h: Vec<_> = (0..omega_pows).map(|n| P.OMEGA.pow_vartime(&[n, 0, 0, 0])).collect();
    assert!(!h.contains(&P.K1));
    assert!(!h.contains(&P.K2));
    let k1_h: Vec<_> = h.iter().map(|r| *r * P.K1).collect();
    assert!(!k1_h.contains(&P.K2));
    let k2_h: Vec<_> = h.iter().map(|r| *r * P.K2).collect();
    let mut h_pows = Matrix::<Fq>::zero(h.len(), h.len());
    for c in 0..h_pows.cols() {
      for r in 0..h_pows.rows() {
        h_pows[(r, c)] = h[r].pow_vartime(&[c as u64, 0, 0, 0]);
      }
    }
    let h_pows_inv = h_pows.inv();
    // let z_h_x = Poly::z(&h);
    let mut z_h_x_coeffs = vec![Fq::zero(); (omega_pows+1).try_into().unwrap()];
    z_h_x_coeffs[0] = -Fq::one();
    z_h_x_coeffs[omega_pows as usize] = Fq::one();
    let z_h_x = Poly::new(z_h_x_coeffs);
    Plonk { srs, h, h_pows_inv, k1_h, k2_h, z_h_x }
  }

  fn interpolate_at_h(&self, vv: &[Fq]) -> Poly<Fq> {
    &self.h_pows_inv * Poly::new(vv.to_vec())
  }

  fn copy_constraint_to_roots(&self, c: &[CopyOf]) -> Vec<Fq> {
    c.iter()
      .map(|c| match c {
        CopyOf::A(n) => self.h[n-1],
        CopyOf::B(n) => self.k1_h[n-1],
        CopyOf::C(n) => self.k2_h[n-1]
      }).collect()
  }

  pub fn prove(
    &self,
    constraints: &Constraints<Fq>,
    assignments: &Assigments<Fq>,
    challenge: &Challenge,
    p: &PlonkTypes,
    rand: [Fq; 9],
  ) -> Proof {
    assert!(constraints.satisfies(assignments));
    let Challenge {
      alpha,
      beta,
      gamma,
      z,
      v
    } = challenge;
    let (omega, k1, k2) = (p.OMEGA, p.K1, p.K2);
    let n = constraints.c_a.len();

    let sigma_1 = self.copy_constraint_to_roots(&constraints.c_a);
    let sigma_2= self.copy_constraint_to_roots(&constraints.c_b);
    let sigma_3 = self.copy_constraint_to_roots(&constraints.c_c);

    let f_a_x = self.interpolate_at_h(&assignments.a);
    let f_b_x = self.interpolate_at_h(&assignments.b);
    let f_c_x = self.interpolate_at_h(&assignments.c);
    let q_o_x = self.interpolate_at_h(&constraints.q_o);
    let q_m_x = self.interpolate_at_h(&constraints.q_m);
    let q_l_x = self.interpolate_at_h(&constraints.q_l);
    let q_r_x = self.interpolate_at_h(&constraints.q_r);
    let q_c_x = self.interpolate_at_h(&constraints.q_c);
  
    let s_sigma_1 = self.interpolate_at_h(&sigma_1);
    let s_sigma_2 = self.interpolate_at_h(&sigma_2);
    let s_sigma_3 = self.interpolate_at_h(&sigma_3);

    let (b1, b2, b3, b4, b5, b6) = (rand[0], rand[1], rand[2], rand[3], rand[4], rand[5]);
    let a_x = Poly::new(vec![b2, b1]) * &self.z_h_x + f_a_x;
    let b_x = Poly::new(vec![b4, b3]) * &self.z_h_x + f_b_x;
    let c_x = Poly::new(vec![b6, b5]) * &self.z_h_x + f_c_x;

    let a_s = self.srs.eval_at_s(&a_x);
    let b_s = self.srs.eval_at_s(&b_x);
    let c_s = self.srs.eval_at_s(&c_x);

    let (b7, b8, b9) = (rand[6], rand[7], rand[8]);
    let mut acc = vec![Fq::one()];
    for i in 1..n as usize {
      let a = assignments.a[i-1];
      let b = assignments.b[i-1];
      let c = assignments.c[i-1];
      let omega_pow = omega.pow(&[(i as u64) - 1, 0, 0, 0]);
      let dend = (a + *beta * omega_pow + gamma) 
        * (b + *beta * omega_pow * k1 + gamma) 
        * (c + *beta * omega_pow * k2 + gamma);
      let dsor = (a + *beta * s_sigma_1.eval(&omega_pow) + gamma)
        * (b + *beta * s_sigma_2.eval(&omega_pow) + gamma)
        * (c + *beta * s_sigma_3.eval(&omega_pow) + gamma);
      let v = acc[i-1] * (dend * dsor.invert().unwrap());
      acc.push(v);
    }
    let acc_x = self.interpolate_at_h(&acc);
    assert!(acc_x.eval(&omega.pow(&[n as u64, 0, 0, 0])) == Fq::one());
    let z_x = Poly::new(vec![b9, b8, b7]) * &self.z_h_x + acc_x;
    let z_s = self.srs.eval_at_s(&z_x);
    
    let lagrange_vector: Vec<_> = std::iter::once(Fq::one())
      .chain(std::iter::repeat(Fq::zero()))
      .take(self.h.len())
      .collect();
    
    let l_1_x = self.interpolate_at_h(&lagrange_vector);
    let p_i_x = Poly::zero();
    let a_x_b_x_q_m_x = (&a_x * &b_x) * &q_m_x;
    let a_x_q_l_x = &a_x * &q_l_x;
    let b_x_q_r_x = &b_x * &q_r_x;
    let c_x_q_o_x = &c_x * &q_o_x;
    let alpha_a_x_beta_x_gamma = &(&a_x + &Poly::new(vec![*gamma, *beta])) * alpha;
    let b_x_beta_k1_x_gamma = &b_x + &Poly::new(vec![*gamma, *beta * k1]);
    let c_x_beta_k2_x_gamma = &c_x + &Poly::new(vec![*gamma, *beta * k2]);
    let z_omega_x = Poly::new(
      z_x.coeffs()
        .iter()
        .enumerate()
        .map(|(n, c)| *c * omega.pow(&[n as u64, 0, 0, 0]))
        .collect::<Vec<_>>(),
    );
    let alpha_a_x_beta_s_sigma1_x_gamma = (&a_x + &s_sigma_1 * beta + gamma) * alpha;
    let b_x_beta_s_sigma2_x_gamma = &b_x + &s_sigma_2 * beta + gamma;
    let c_x_beta_s_sigma3_x_gamma = &c_x + &s_sigma_3 * beta + gamma;
    let alpha_2_z_x_1_l_1_x = ((&z_x + Poly::new(vec![-Fq::one()])) * alpha.pow(&[2, 0, 0, 0])) * &l_1_x;
    let t_1_z_h = a_x_b_x_q_m_x + a_x_q_l_x + b_x_q_r_x + c_x_q_o_x + p_i_x + &q_c_x;
    let t_2_z_h = alpha_a_x_beta_x_gamma * b_x_beta_k1_x_gamma * c_x_beta_k2_x_gamma * &z_x;
    let t_3_z_h = alpha_a_x_beta_s_sigma1_x_gamma
      * b_x_beta_s_sigma2_x_gamma
      * c_x_beta_s_sigma3_x_gamma
      * &z_omega_x;
    let t_4_z_h = alpha_2_z_x_1_l_1_x;
    let (t_x, rem) = (t_1_z_h + t_2_z_h - t_3_z_h + t_4_z_h) / self.z_h_x.clone();
    assert_eq!(rem, Poly::zero());
    let t_hi_x = Poly::new(t_x.coeffs()[2*n+4..3*n+6].to_owned());
    let t_mid_x = Poly::new(t_x.coeffs()[n+2..2*n+4].to_owned());
    let t_lo_x = Poly::new(t_x.coeffs()[0..n+2].to_owned());

    let t_hi_s = self.srs.eval_at_s(&t_hi_x);
    let t_mid_s = self.srs.eval_at_s(&t_mid_x);
    let t_lo_s = self.srs.eval_at_s(&t_lo_x);

    let a_z = a_x.eval(z);
    let b_z = b_x.eval(z);
    let c_z = c_x.eval(z);
    let s_sigma_1_z = s_sigma_1.eval(z);
    let s_sigma_2_z = s_sigma_2.eval(z);
    let z_omega_z = z_omega_x.eval(z);
    let a_z_b_z_q_m_x = &q_m_x * a_z * b_z;
    let a_z_q_l_x = &q_l_x * a_z;
    let b_z_q_r_x = &q_r_x * b_z;
    let c_z_q_o_x = &q_o_x * c_z;
    let r_1_x = a_z_b_z_q_m_x + a_z_q_l_x + b_z_q_r_x + c_z_q_o_x + q_c_x;
    let r_2_x = &z_x
      * ((a_z + *beta * z + gamma)
      * (b_z + *beta * k1 * z + gamma)
      * (c_z + *beta * k2 * z + gamma)
      * alpha);

    let r_3_x = 
      (&s_sigma_3 * *beta + gamma + c_z)
      * (a_z + *beta * s_sigma_1_z + gamma) 
      * (b_z + *beta * s_sigma_2_z + gamma)
      * z_omega_z * alpha;

    let r_4_x = (&z_x + Poly::new(vec![-Fq::one()])) * l_1_x.eval(z) * alpha.pow(&[2, 0, 0, 0]);
    let r_x = r_1_x + r_2_x - r_3_x + r_4_x 
      - (t_lo_x + t_mid_x * z.pow(&[n as u64 + 2, 0, 0, 0]) + t_hi_x * z.pow(&[2 * n as u64 + 4, 0, 0, 0])) * self.z_h_x.eval(z);

    let w_z_x = r_x
      + (a_x - a_z) * v
      + (b_x - b_z) * v.pow(&[2, 0, 0, 0])
      + (c_x - c_z) * v.pow(&[3, 0, 0, 0])
      + (s_sigma_1 - s_sigma_1_z) * v.pow(&[4, 0, 0, 0])
      + (s_sigma_2 - s_sigma_2_z) * v.pow(&[5, 0, 0, 0]);
    
    let (w_z_x, rem) = w_z_x / Poly::new(vec![-*z, Fq::one()]);
    assert_eq!(rem, Poly::zero());

    let (w_z_omega_x, rem) = (z_x - z_omega_z) / Poly::new(vec![-*z * omega, Fq::one()]);
    assert_eq!(rem, Poly::zero());
    let w_z_s = self.srs.eval_at_s(&w_z_x);
    let w_z_omega_s = self.srs.eval_at_s(&w_z_omega_x);
    Proof {
      a_s,
      b_s,
      c_s,
      z_s,
      t_lo_s,
      t_mid_s,
      t_hi_s,
      w_z_s,
      w_z_omega_s,
      a_z,
      b_z,
      c_z,
      s_sigma_1_z,
      s_sigma_2_z,
      z_omega_z,
    }
  }

  pub fn verify(
    &self,
    constraints: &Constraints<Fq>,
    proof: &Proof,
    challenge: &Challenge,
    p: &PlonkTypes,
    rand: [Fq; 1],
  ) -> bool {
    let Proof {
      a_s,
      b_s,
      c_s,
      z_s,
      t_lo_s,
      t_mid_s,
      t_hi_s,
      w_z_s,
      w_z_omega_s,
      a_z,
      b_z,
      c_z,
      s_sigma_1_z,
      s_sigma_2_z,
      z_omega_z,
    } = proof;

    let Challenge {
      alpha,
      beta,
      gamma,
      z,
      v,
    } = challenge;

    let (omega, k1, k2) = (p.OMEGA, p.K1, p.K2);
    let sigma_1 = self.copy_constraint_to_roots(&constraints.c_a);
    let sigma_2 = self.copy_constraint_to_roots(&constraints.c_b);
    let sigma_3 = self.copy_constraint_to_roots(&constraints.c_c);
    let q_m_s = self.srs.eval_at_s(&self.interpolate_at_h(&constraints.q_m));
    let q_l_s = self.srs.eval_at_s(&self.interpolate_at_h(&constraints.q_l));
    let q_r_s = self.srs.eval_at_s(&self.interpolate_at_h(&constraints.q_r));
    let q_o_s = self.srs.eval_at_s(&self.interpolate_at_h(&constraints.q_o));
    let q_c_s = self.srs.eval_at_s(&self.interpolate_at_h(&constraints.q_c));
    let sigma_1_s = self.srs.eval_at_s(&self.interpolate_at_h(&sigma_1));
    let sigma_2_s = self.srs.eval_at_s(&self.interpolate_at_h(&sigma_2));
    let sigma_3_s = self.srs.eval_at_s(&self.interpolate_at_h(&sigma_3));
    let u = rand[0];

    if !bool::from(a_s.is_on_curve()) 
      || !bool::from(b_s.is_on_curve())
      || !bool::from(c_s.is_on_curve())
      || !bool::from(z_s.is_on_curve())
      || !bool::from(t_lo_s.is_on_curve())
      || !bool::from(t_mid_s.is_on_curve())
      || !bool::from(t_hi_s.is_on_curve())
      || !bool::from(w_z_s.is_on_curve())
      || !bool::from(w_z_omega_s.is_on_curve())
    {
      return false;
    }

    // if !a_z.is()
    //   || !b_z.in_field()
    //   || !c_z.in_field()
    //   || !s_sigma_1_z.in_field()
    //   || !s_sigma_2_z.in_field()
    //   || !r_z.in_field()
    //   || !z_omega_z.in_field()
    // {
    //   return false;
    // }

    let z_h_z = self.z_h_x.eval(z);
    let lagrange_vector: Vec<_> = std::iter::once(Fq::one())
    .chain(std::iter::repeat(Fq::zero()))
    .take(self.h.len())
    .collect();
    let l_1_z = self.interpolate_at_h(&lagrange_vector).eval(z);
    let p_i_z = Fq::zero();
    let a_z_beta_s_sigma_1_z_gamma = *beta * s_sigma_1_z + gamma + a_z;
    let b_z_beta_s_sigma_2_z_gamma = *beta * s_sigma_2_z + gamma + b_z;
    let c_z_gamma = *c_z + gamma;
    let l_1_z_alpha_2 = l_1_z * alpha.pow(&[2, 0, 0, 0]);

    let r_0 = -l_1_z_alpha_2
      - alpha * (a_z_beta_s_sigma_1_z_gamma)
      * b_z_beta_s_sigma_2_z_gamma
      * c_z_gamma
      * z_omega_z;

    // let t_z = (*r_z + p_i_z
    //   - (a_z_beta_s_sigma_1_z_gamma * b_z_beta_s_sigma_2_z_gamma * c_z_gamma * z_omega_z)
    //   - l_1_z_alpha_2)
    //   * z_h_z.invert().unwrap();
    
    let d_1_s = q_m_s * (*a_z * *b_z)
      + q_l_s * (*a_z)
      + q_r_s * (*b_z)
      + q_o_s * (*c_z)
      + q_c_s;
    let d_2_s = *z_s
      * (
        (*a_z + *beta * z + gamma)
          * (*b_z + *beta * k1 * z + gamma)
          * (*c_z + *beta * k2 * z + gamma)
          * alpha
          + l_1_z * alpha.pow(&[2, 0, 0, 0])
          + u
      );
    let d_3_s = sigma_3_s
      * (
      (*a_z + *beta * s_sigma_1_z + gamma)
        * (*b_z + *beta * s_sigma_2_z + gamma)
        * alpha
        * beta
        * z_omega_z
      );
    
    let n = constraints.c_a.len() as u64;
    let d_4_s = &z_h_z * (t_lo_s + z.pow(&[n + 2, 0, 0, 0]) * t_mid_s + z.pow(&[2 * n + 4, 0, 0, 0]) * t_hi_s);

    let d_s = d_1_s + d_2_s - d_3_s - d_4_s;
    
    let f_s = d_s
      + a_s.to_owned() * v
      + b_s.to_owned() * v.pow(&[2 ,0, 0, 0])
      + c_s.to_owned() * v.pow(&[3 ,0, 0, 0])
      + sigma_1_s.to_owned() * v.pow(&[4 ,0, 0, 0])
      + sigma_2_s.to_owned() * v.pow(&[5 ,0, 0, 0]);
    
    let e_s = self.srs.eval_at_s(&Poly::from(&[1]))
      * (
          -r_0
            + v * a_z
            + v.pow(&[2 ,0, 0, 0]) * b_z
            + v.pow(&[3 ,0, 0, 0]) * c_z
            + v.pow(&[4 ,0, 0, 0]) * s_sigma_1_z
            + v.pow(&[5 ,0, 0, 0]) * s_sigma_2_z
            + u * z_omega_z
      );
    let e_1_q1 = *w_z_s + *w_z_omega_s * u;
    let e_1_q2 = self.srs.g2_s;
    let e_2_q1 = *w_z_s * z + *w_z_omega_s * u * z * omega + f_s - e_s;
    let e_2_q2 = self.srs.g2_1;
    
    let e_1 = pairing(&G1Affine::from(&e_1_q1), &G2Affine::from(&e_1_q2));
    let e_2 = pairing(&G1Affine::from(e_2_q1), &G2Affine::from(e_2_q2));
    e_1 == e_2

  }

}



