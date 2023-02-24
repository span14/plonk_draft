pub mod constraints;
pub mod fft;
pub mod matrix;
pub mod plonk;
pub mod poly;

use ff::{PrimeField, Field};
use bls12_381::Scalar as Fq;
use constraints::{Constraints, Gate, CopyOf, Assigment, Assigments};
use plonk::{PlonkTypes, Plonk, Challenge, SRS};
use rand::prelude::*;
use num_bigint::BigUint;

fn to_fq(val: u64) -> Fq {
  Fq::from_raw([val, 0, 0, 0])
}

fn to_u64_array(val: [u8; 32]) -> [u64; 4] {
  let mut res: [u64; 4] = [0; 4];
  for i in 0..4 {
    res[i] = u64::from_le_bytes(val[i*8..i*8+8].try_into().unwrap());
  }
  res
}

#[allow(unused_variables)]
fn main() {
  let mut rng = rand::thread_rng();
  let s = Fq::random(rng.clone());
  let srs = SRS::create(s, 6);

  let MODULUS = Fq::from_raw([
    0xffff_ffff_0000_0001,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
  ]);
  // G^T where T * 2^32 = p-1
  // let root = Fq::root_of_unity();
  // let t = BigUint::from_bytes_le(&(MODULUS-Fq::from(1)).to_bytes());
  // println!("{}", (t.clone() - ( t.clone() % (7 as u64)) / (7 as u64)));
  // x1 * x1 = x4
  // x2 * x2 = x5
  // x3 * x3 = x6
  // x4 + x5 = x6
  // constraints and assigments
  let constraints = Constraints::<Fq>::new(
    &[
        Gate::mul_a_b(),
        Gate::mul_a_b(),
        Gate::mul_a_b(),
        Gate::sum_a_b(),
    ],
    (
        vec![CopyOf::B(1), CopyOf::B(2), CopyOf::B(3), CopyOf::C(1)],
        vec![CopyOf::A(1), CopyOf::A(2), CopyOf::A(3), CopyOf::C(2)],
        vec![CopyOf::A(4), CopyOf::B(4), CopyOf::C(4), CopyOf::C(3)],
    ),
  );

  let assigments = Assigments::new(&[
      Assigment::new(to_fq(3), to_fq(3), to_fq(9)),
      Assigment::new(to_fq(4), to_fq(4), to_fq(16)),
      Assigment::new(to_fq(5), to_fq(5), to_fq(25)),
      Assigment::new(to_fq(9), to_fq(16), to_fq(25)),
  ]);

  let t = BigUint::from_bytes_le(&(MODULUS-Fq::from(1)).to_bytes());
  assert_eq!(t.clone() % (4 as u64), BigUint::from(0 as u64));
  
  let root_of_unity = t / (4 as u64);
  let PlonkByHandTypes: PlonkTypes = PlonkTypes {
    K1: Fq::from(2),
    K2: Fq::from(3),
    OMEGA: Fq::multiplicative_generator().pow(&to_u64_array(root_of_unity.to_bytes_le().try_into().unwrap()))
  };
  let plonk = Plonk::new(
      srs,
      4, // omega pows
      &PlonkByHandTypes
  );

  // // random numbers (the b's)
  let rand = [
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
    Fq::random(rng.clone()),
  ];

  // // values that are sent from the verifier to the prover
  let challenge = Challenge {
      alpha: Fq::random(rng.clone()),
      beta: Fq::random(rng.clone()),
      gamma: Fq::random(rng.clone()),
      z: Fq::random(rng.clone()),
      v: Fq::random(rng.clone()),
  };

  let proof = plonk.prove(&constraints, &assigments, &challenge, &PlonkByHandTypes, rand);
  let rand = [Fq::random(rng.clone())];
  assert!(plonk.verify(&constraints, &proof, &challenge, &PlonkByHandTypes, rand));
  println!("Verify Successfully");
}