use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, SynthesisError, LinearCombination,
};
use ff::{PrimeField, PrimeFieldBits};

use crate::{field::{Fe25519, SQRT_MINUS_ONE, MINUS_ONE}, curve::SQRT_AD_MINUS_ONE};
use crate::curve::{AffinePoint, D, ONE_MINUS_D_SQUARED, D_MINUS_ONE_SQUARED};

pub struct AllocatedAffinePoint<F: PrimeField> {
    x: AllocatedNum<F>,
    y: AllocatedNum<F>,
}

impl<F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits> AllocatedAffinePoint<F> {
    pub fn alloc_affine_point<CS>(cs: &mut CS, x: F, y: F) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {   
        let point = AffinePoint {
            x: Fe25519::from_repr(x.to_repr()).unwrap(),
            y: Fe25519::from_repr(y.to_repr()).unwrap()
        };
        assert!(point.is_on_curve());

        let x_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc x"), || Ok(x))?;
        let y_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc y"), || Ok(y))?;
        Ok(AllocatedAffinePoint {
            x: x_alloc,
            y: y_alloc,
        })
    }

    pub fn add<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>
    where 
        CS: ConstraintSystem<F>,
    {   
        let p = AffinePoint{
            x: Fe25519::from_repr(self.x.get_value().unwrap().to_repr()).unwrap(),
            y: Fe25519::from_repr(self.y.get_value().unwrap().to_repr()).unwrap(),
        };
        let q = AffinePoint{
            x: Fe25519::from_repr(other.x.get_value().unwrap().to_repr()).unwrap(),
            y: Fe25519::from_repr(other.y.get_value().unwrap().to_repr()).unwrap(),
        };
        assert!(p.is_on_curve());
        assert!(q.is_on_curve());
        
        let d = F::from_repr(D.to_repr()).unwrap();

        let x1_x2  = self.x.mul(&mut cs.namespace(|| "x1 * x2"), &other.x)?;
        let x1_y2  = self.x.mul(&mut cs.namespace(|| "x1 * y2"), &other.y)?;
        let y1_y2  = self.y.mul(&mut cs.namespace(|| "y1 * y2"), &other.y)?;
        let y1_x2  = self.y.mul(&mut cs.namespace(|| "y1 * x2"), &other.x)?;

        let prod = x1_x2.mul(&mut cs.namespace(|| "x1 * x2 * y1 * y2"), &y1_y2)?;

        let out = p + q;
        let out_alloc = Self::alloc_affine_point(
            &mut cs.namespace(|| "alloc out"), 
            F::from_repr(out.x.to_repr()).unwrap(), 
            F::from_repr(out.y.to_repr()).unwrap(), 
        )?;

        cs.enforce(
            || "out_x * (1 + d * x1 * x2 * y1 * y2) === x1 * y2 + x2 * y1", 
            |lc| lc + out_alloc.x.get_variable() , 
            |lc| lc + CS::one() + &LinearCombination::from_coeff(prod.get_variable(), d), 
            |lc| lc + x1_y2.get_variable() + y1_x2.get_variable()
        );
        cs.enforce(
            || "out_y * (1 - d * x1 * x2 * y1 * y2) === x1 * x2 + y1 * y2", 
            |lc| lc + out_alloc.y.get_variable() , 
            |lc| lc + CS::one() - &LinearCombination::from_coeff(prod.get_variable(), d), 
            |lc| lc + x1_x2.get_variable() + y1_y2.get_variable()
        );

        Ok(out_alloc)

    }

    pub fn map_to_curve<CS>(cs: &mut CS, t: AllocatedNum<F>) -> Result<Self, SynthesisError>
    where 
        CS: ConstraintSystem<F>,
    {
        let i = F::from_repr(SQRT_MINUS_ONE.to_repr()).unwrap();
        let d = F::from_repr(D.to_repr()).unwrap();
        let one_minus_d_sq = F::from_repr(ONE_MINUS_D_SQUARED.to_repr()).unwrap();
        let d_minus_one_sq = F::from_repr(D_MINUS_ONE_SQUARED.to_repr()).unwrap();
        let c = F::from_repr(MINUS_ONE.to_repr()).unwrap();
        let sqrt_ad_minus_one = F::from_repr(SQRT_AD_MINUS_ONE.to_repr()).unwrap();
        
        let r = AllocatedNum::alloc(
            &mut cs.namespace(|| "Alloc r"), 
            { 
                || 
                {
                    let mut tmp = t.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                    tmp.mul_assign(tmp);
                    tmp.mul_assign(i);
                    Ok(tmp)
                }
            }
        )?;
        cs.enforce( 
            || "r === i (t * t)", 
            |lc| lc + &LinearCombination::from_coeff(t.get_variable(), i), 
            |lc| lc + t.get_variable(), 
            |lc| lc + r.get_variable()
        );
        
        let u = AllocatedNum::alloc(
            &mut cs.namespace(|| "Alloc u"), 
            { 
                || 
                {
                    let mut tmp = r.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                    tmp.add_assign(F::ONE);
                    tmp.mul_assign(one_minus_d_sq);
                    Ok(tmp)
                }
            }
        )?;
        cs.enforce( 
            || "u === (r + one) * one_minus_d_sq", 
            |lc| lc + r.get_variable() + CS::one(), 
            |lc| lc + &LinearCombination::from_coeff(CS::one(), one_minus_d_sq), 
            |lc| lc + u.get_variable()
        );
        let is_u_zero = u.is_zero(&mut cs.namespace(|| "u == 0"))?;

        let v = AllocatedNum::alloc(
            &mut cs.namespace(|| "Alloc v"), 
            { 
                || 
                {   
                    let r_val = r.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                    Ok((c - d * r_val) * (r_val + d))
                }
            }
        )?;
        cs.enforce( 
            || "v === (c - d * r) * (r + d)", 
            |lc: LinearCombination<F>| lc + &LinearCombination::from_coeff(CS::one(), c) - &LinearCombination::from_coeff(r.get_variable(), d), 
            |lc| lc + r.get_variable() + &LinearCombination::from_coeff(CS::one(), d), 
            |lc| lc + v.get_variable()
        );
        let is_v_zero = v.is_zero(&mut cs.namespace(|| "v == 0"))?;

        let u_by_v = AllocatedNum::alloc(
            &mut cs.namespace(|| "alloc u by v"), 
            || {
                let u_val = u.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let v_val = v.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                if  v_val == F::ZERO {
                    Ok(F::ZERO)
                } else {
                    let v_inv = v_val.invert();
                    assert!(bool::from(v_inv.is_some()));
                    let v_inv = v_inv.unwrap();
                    Ok(u_val * v_inv)
                }
            }
        )?;
        cs.enforce( 
            || "u === u_by_v * v", 
            |lc: LinearCombination<F>| lc + u_by_v.get_variable(),
            |lc| lc + v.get_variable(), 
            |lc| lc + u.get_variable()
        );

        let iu_by_v = AllocatedNum::alloc(
            &mut cs.namespace(|| "alloc i * (u by v)"), 
            || {
                let u_val = u.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                let v_val = v.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                if  v_val == F::ZERO {
                    Ok(F::ZERO)
                } else {
                    let v_inv = v_val.invert();
                    assert!(bool::from(v_inv.is_some()));
                    let v_inv = v_inv.unwrap();
                    Ok(i * u_val * v_inv)
                }
            }
        )?;
        cs.enforce( 
            || " (i*u) === iu_by_v * v", 
            |lc: LinearCombination<F>| lc + iu_by_v.get_variable(),
            |lc| lc + v.get_variable(), 
            |lc| lc + &LinearCombination::from_coeff(u.get_variable(), i)
        );

        let mut s = AllocatedNum::alloc(
            &mut cs.namespace(|| "Alloc square root"), 
            || {
                let u_val = Fe25519::from_repr(u.get_value().ok_or(SynthesisError::AssignmentMissing)?.to_repr());
                assert!(bool::from(u_val.is_some()));
                let u_val = u_val.unwrap();
                
                let v_val = Fe25519::from_repr(v.get_value().ok_or(SynthesisError::AssignmentMissing)?.to_repr());
                assert!(bool::from(v_val.is_some()));
                let v_val = v_val.unwrap();
                
                let (_, s_val ) = Fe25519::sqrt_ratio_i(u_val, v_val);
                let s_val = F::from_repr(s_val.to_repr());
                assert!(bool::from(s_val.is_some()));
                let s_val = s_val.unwrap();
                Ok(s_val)
            }
        )?;
        
        let s_sq = s.square(&mut cs.namespace(|| "s * s"))?;
        let is_s_sq_equal_u_by_v = s_sq.is_equal(&mut cs.namespace(|| "s_sq == u_by_v"), &u_by_v)?;
        let cond1 = Boolean::and(&mut cs.namespace(|| "not(is_v_zero) & is_s_sq_equal_u_by_v"), &is_v_zero.not(), &is_s_sq_equal_u_by_v)?;
        let is_sq_exp = Boolean::or(
            &mut cs.namespace(|| "(not(is_v_zero) & is_s_sq_equal_u_by_v) | is_u_zero"), 
            &cond1, 
            &is_u_zero
        )?;
        
        let is_sq = Boolean::from(
            AllocatedBit::alloc(
                &mut cs.namespace(|| "alloc is_sq"),
                {
                    let u_val = Fe25519::from_repr(u.get_value().ok_or(SynthesisError::AssignmentMissing)?.to_repr());
                    assert!(bool::from(u_val.is_some()));
                    let u_val = u_val.unwrap();
                
                    let v_val = Fe25519::from_repr(v.get_value().ok_or(SynthesisError::AssignmentMissing)?.to_repr());
                    assert!(bool::from(v_val.is_some()));
                    let v_val = v_val.unwrap();
                
                    let (is_sq_val, _ ) = Fe25519::sqrt_ratio_i(u_val, v_val);
                    Some(is_sq_val.unwrap_u8() == 1u8)
                }
            )?
        );
        
        assert!(
            Boolean::enforce_equal(
                &mut cs.namespace(|| "constraint is_sq"), 
                &is_sq, 
                &is_sq_exp
            ).is_ok()
        );

        cs.enforce(
            || "constarint s: (iu_by_v - u_by_v) * is_sq === iu_by_v - s_sq", 
            |lc| lc + iu_by_v.get_variable() - u_by_v.get_variable(), 
            |lc| lc + &is_sq.lc(CS::one(), F::ONE), 
            |lc| lc + iu_by_v.get_variable() - s_sq.get_variable()
        );

        let mut s_prime = s.mul(&mut cs.namespace(|| "s * t"), &t)?;
        let s_prime_is_pos = is_negative(&mut cs.namespace(|| "check s_prime is neg"), s_prime.clone())?.not();
        let s_prime_neg = s_prime.clone().neg(&mut cs.namespace(|| "negative s_prime"))?;
        s_prime = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select s_prime"), 
            &s_prime, 
            &s_prime_neg, 
            &s_prime_is_pos
        )?;

        s = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select s"), 
            &s, 
            &s_prime, 
            &is_sq.not()
        )?;
        
        let mut c_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc c"), || Ok(c))?;
        c_alloc = AllocatedNum::conditionally_select(
            &mut cs.namespace(|| "select c_alloc"), 
            &c_alloc, 
            &r, 
            &is_sq.not()
        )?;

        let n = AllocatedNum::alloc(
            &mut cs.namespace(|| "alloc n"),
            || {
                let mut tmp = c_alloc.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                tmp.mul_assign(r.get_value().ok_or(SynthesisError::AssignmentMissing)? - F::ONE);
                tmp.mul_assign(d_minus_one_sq);
                tmp.sub_assign(v.get_value().ok_or(SynthesisError::AssignmentMissing)?);
                Ok(tmp)
            } 
        )?;
        cs.enforce(
            || "n + v === (d_minus_one_sq * c_alloc) * (r - one)", 
            |lc| lc + &LinearCombination::from_coeff(c_alloc.get_variable(), d_minus_one_sq), 
            |lc| lc + r.get_variable() - CS::one(), 
            |lc| lc + n.get_variable() + v.get_variable()
        );

        let one_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc one"), || Ok(F::ONE))?;

        let w0 = AllocatedNum::alloc(
            &mut cs.namespace(|| "alloc w0"), 
            || {
                let mut tmp = s.get_value().ok_or(SynthesisError::AssignmentMissing)?;
                tmp.add_assign(tmp);
                tmp.mul_assign(v.get_value().ok_or(SynthesisError::AssignmentMissing)?);
                Ok(tmp)
            }
        )?;
        cs.enforce(
            || "w0 === (s + s) * v", 
            |lc| lc + s.get_variable() + s.get_variable(), 
            |lc| lc + v.get_variable(), 
            |lc| lc + w0.get_variable()
        );

        let new_s_sq = s.square(&mut cs.namespace(|| "calc new s_sq"))?;
        let w1 = AllocatedNum::alloc(
            &mut cs.namespace(|| "alloc w1"), 
            || {
                Ok(n.get_value().ok_or(SynthesisError::AssignmentMissing)? * sqrt_ad_minus_one)
            }
        )?;
        cs.enforce(
            || "w1 === n * sqrt_ad_minus_one", 
            |lc| lc + CS::one(), 
            |lc| lc + &LinearCombination::from_coeff(n.get_variable(), sqrt_ad_minus_one), 
            |lc| lc + w1.get_variable()
        );
        let w2 = one_alloc.sub(&mut cs.namespace(|| "calc w2"), &new_s_sq)?;
        let w3 = one_alloc.add(&mut cs.namespace(|| "calc w3"), &new_s_sq)?;
        
        let x_coor = w0.div(&mut cs.namespace(|| "calc x_coor"), &w1)?;
        let y_coor = w2.div(&mut cs.namespace(|| "calc y_coor"), &w3)?;

        let point = AffinePoint {
            x: Fe25519::from_repr(x_coor.get_value().ok_or(SynthesisError::AssignmentMissing)?.to_repr()).unwrap(),
            y: Fe25519::from_repr(y_coor.get_value().ok_or(SynthesisError::AssignmentMissing)?.to_repr()).unwrap()
        };
        assert!(point.is_on_curve());

        Ok(
            AllocatedAffinePoint { x: x_coor, y: y_coor }
        )
    }

    pub fn elligator2<CS>(cs: &mut CS, bytes: &[u8; 64]) -> Result<Self, SynthesisError> 
    where 
        CS: ConstraintSystem<F>
    {
        let mut r_1_bytes = [0u8; 32];
        r_1_bytes.copy_from_slice(&bytes[0..32]);
        let r_1 = AllocatedNum::alloc(
            &mut cs.namespace(|| "alloc r_1"), 
            || {
                let z = F::from_repr(Fe25519::from_bytes(r_1_bytes).to_repr());
                assert!(bool::from(z.is_some()));
                Ok(z.unwrap())
            }
        )?;
        let p = AllocatedAffinePoint::map_to_curve(&mut cs.namespace(|| "map r_1"), r_1)?;

        let mut r_2_bytes = [0u8; 32];
        r_2_bytes.copy_from_slice(&bytes[32..64]);
        let r_2 = AllocatedNum::alloc(
            &mut cs.namespace(|| "alloc r_2"), 
            || {
                let z = F::from_repr(Fe25519::from_bytes(r_2_bytes).to_repr());
                assert!(bool::from(z.is_some()));
                Ok(z.unwrap())
            }
        )?;
        let q = AllocatedAffinePoint::map_to_curve(&mut cs.namespace(|| "map r_2"), r_2)?;

        p.add(&mut cs.namespace(|| "p + q"), &q)
    }
}

pub fn is_negative<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(cs: &mut CS, num: AllocatedNum<F>) -> Result<Boolean, SynthesisError> {
    let bits = num.to_bits_le_strict(&mut cs.namespace(|| "deconstruct num"))?;
    Boolean::and(&mut cs.namespace(|| "bits[0] & 1"), &bits[0], &Boolean::constant(true))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve::Ed25519Curve;
    use ff::Field;
    use bellpepper_core::test_cs::TestConstraintSystem;

    pub fn random_point() -> AffinePoint {
        let mut rng = rand::thread_rng();
        let mut point = AffinePoint::default();
        loop {
            let y = Fe25519::random(&mut rng);
            let y_sq = y.square();
            let x_sq = (y_sq - Fe25519::ONE) * (D*y_sq + Fe25519::ONE).invert().unwrap();

            let x = x_sq.sqrt();
            if bool::from(x.is_some()) {
                point.x = x.unwrap();
                point.y = y;
                break;
            }
        }
        point
    }

    #[test]
    fn test_add_circuit() {
        let p = random_point();
        assert!(Ed25519Curve::is_on_curve(&p));
        let q = random_point();
        assert!(Ed25519Curve::is_on_curve(&q));
        let out_exp = p + q;
        
        let mut cs = TestConstraintSystem::<Fe25519>::new();
        let p_alloc = AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc p"), p.x, p.y).unwrap();
        let q_alloc = AllocatedAffinePoint::alloc_affine_point(&mut cs.namespace(|| "alloc q"), q.x, q.y).unwrap();

        let out_alloc = p_alloc.add(&mut cs.namespace(|| "add"), &q_alloc).unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 7);
        assert_eq!(out_exp.x, out_alloc.x.get_value().unwrap());
        assert_eq!(out_exp.y, out_alloc.y.get_value().unwrap()); 
    }

    #[test]
    fn test_m2c_circuit() {

        // test vectors copied from https://doc.dalek.rs/src/curve25519_dalek/ristretto.rs.html#1066
        let bytes: [[u8; 32]; 16] = [
            [
                184, 249, 135, 49, 253, 123, 89, 113, 67, 160, 6, 239, 7, 105, 211, 41, 192, 249,
                185, 57, 9, 102, 70, 198, 15, 127, 7, 26, 160, 102, 134, 71,
            ],
            [
                229, 14, 241, 227, 75, 9, 118, 60, 128, 153, 226, 21, 183, 217, 91, 136, 98, 0,
                231, 156, 124, 77, 82, 139, 142, 134, 164, 169, 169, 62, 250, 52,
            ],
            [
                115, 109, 36, 220, 180, 223, 99, 6, 204, 169, 19, 29, 169, 68, 84, 23, 21, 109,
                189, 149, 127, 205, 91, 102, 172, 35, 112, 35, 134, 69, 186, 34,
            ],
            [
                16, 49, 96, 107, 171, 199, 164, 9, 129, 16, 64, 62, 241, 63, 132, 173, 209, 160,
                112, 215, 105, 50, 157, 81, 253, 105, 1, 154, 229, 25, 120, 83,
            ],
            [
                156, 131, 161, 162, 236, 251, 5, 187, 167, 171, 17, 178, 148, 210, 90, 207, 86, 21,
                79, 161, 167, 215, 234, 1, 136, 242, 182, 248, 38, 85, 79, 86,
            ],
            [
                251, 177, 124, 54, 18, 101, 75, 235, 245, 186, 19, 46, 133, 157, 229, 64, 10, 136,
                181, 185, 78, 144, 254, 167, 137, 49, 107, 10, 61, 10, 21, 25,
            ],
            [
                232, 193, 20, 68, 240, 77, 186, 77, 183, 40, 44, 86, 150, 31, 198, 212, 76, 81, 3,
                217, 197, 8, 126, 128, 126, 152, 164, 208, 153, 44, 189, 77,
            ],
            [
                173, 229, 149, 177, 37, 230, 30, 69, 61, 56, 172, 190, 219, 115, 167, 194, 71, 134,
                59, 75, 28, 244, 118, 26, 162, 97, 64, 16, 15, 189, 30, 64,
            ],
            [
                106, 71, 61, 107, 250, 117, 42, 151, 91, 202, 212, 100, 52, 188, 190, 21, 125, 218,
                31, 18, 253, 241, 160, 133, 57, 242, 3, 164, 189, 68, 111, 75,
            ],
            [
                112, 204, 182, 90, 220, 198, 120, 73, 173, 107, 193, 17, 227, 40, 162, 36, 150,
                141, 235, 55, 172, 183, 12, 39, 194, 136, 43, 153, 244, 118, 91, 89,
            ],
            [
                111, 24, 203, 123, 254, 189, 11, 162, 51, 196, 163, 136, 204, 143, 10, 222, 33,
                112, 81, 205, 34, 35, 8, 66, 90, 6, 164, 58, 170, 177, 34, 25,
            ],
            [
                225, 183, 30, 52, 236, 82, 6, 183, 109, 25, 227, 181, 25, 82, 41, 193, 80, 77, 161,
                80, 242, 203, 79, 204, 136, 245, 131, 110, 237, 106, 3, 58,
            ],
            [
                207, 246, 38, 56, 30, 86, 176, 90, 27, 200, 61, 42, 221, 27, 56, 210, 79, 178, 189,
                120, 68, 193, 120, 167, 77, 185, 53, 197, 124, 128, 191, 126,
            ],
            [
                1, 136, 215, 80, 240, 46, 63, 147, 16, 244, 230, 207, 82, 189, 74, 50, 106, 169,
                138, 86, 30, 131, 214, 202, 166, 125, 251, 228, 98, 24, 36, 21,
            ],
            [
                210, 207, 228, 56, 155, 116, 207, 54, 84, 195, 251, 215, 249, 199, 116, 75, 109,
                239, 196, 251, 194, 246, 252, 228, 70, 146, 156, 35, 25, 39, 241, 4,
            ],
            [
                34, 116, 123, 9, 8, 40, 93, 189, 9, 103, 57, 103, 66, 227, 3, 2, 157, 107, 134,
                219, 202, 74, 230, 154, 78, 107, 219, 195, 214, 14, 84, 80,
            ],
        ];

        let out: [[u8; 32]; 16] = [
            [
                176, 157, 237, 97, 66, 29, 140, 166, 168, 94, 26, 157, 212, 216, 229, 160, 195,
                246, 232, 239, 169, 112, 63, 193, 64, 32, 152, 69, 11, 190, 246, 86,
            ],
            [
                234, 141, 77, 203, 181, 225, 250, 74, 171, 62, 15, 118, 78, 212, 150, 19, 131, 14,
                188, 238, 194, 244, 141, 138, 166, 162, 83, 122, 228, 201, 19, 26,
            ],
            [
                232, 231, 51, 92, 5, 168, 80, 36, 173, 179, 104, 68, 186, 149, 68, 40, 140, 170,
                27, 103, 99, 140, 21, 242, 43, 62, 250, 134, 208, 255, 61, 89,
            ],
            [
                208, 120, 140, 129, 177, 179, 237, 159, 252, 160, 28, 13, 206, 5, 211, 241, 192,
                218, 1, 97, 130, 241, 20, 169, 119, 46, 246, 29, 79, 80, 77, 84,
            ],
            [
                202, 11, 236, 145, 58, 12, 181, 157, 209, 6, 213, 88, 75, 147, 11, 119, 191, 139,
                47, 142, 33, 36, 153, 193, 223, 183, 178, 8, 205, 120, 248, 110,
            ],
            [
                26, 66, 231, 67, 203, 175, 116, 130, 32, 136, 62, 253, 215, 46, 5, 214, 166, 248,
                108, 237, 216, 71, 244, 173, 72, 133, 82, 6, 143, 240, 104, 41,
            ],
            [
                40, 157, 102, 96, 201, 223, 200, 197, 150, 181, 106, 83, 103, 126, 143, 33, 145,
                230, 78, 6, 171, 146, 210, 143, 112, 5, 245, 23, 183, 138, 18, 120,
            ],
            [
                220, 37, 27, 203, 239, 196, 176, 131, 37, 66, 188, 243, 185, 250, 113, 23, 167,
                211, 154, 243, 168, 215, 54, 171, 159, 36, 195, 81, 13, 150, 43, 43,
            ],
            [
                232, 121, 176, 222, 183, 196, 159, 90, 238, 193, 105, 52, 101, 167, 244, 170, 121,
                114, 196, 6, 67, 152, 80, 185, 221, 7, 83, 105, 176, 208, 224, 121,
            ],
            [
                226, 181, 183, 52, 241, 163, 61, 179, 221, 207, 220, 73, 245, 242, 25, 236, 67, 84,
                179, 222, 167, 62, 167, 182, 32, 9, 92, 30, 165, 127, 204, 68,
            ],
            [
                226, 119, 16, 242, 200, 139, 240, 87, 11, 222, 92, 146, 156, 243, 46, 119, 65, 59,
                1, 248, 92, 183, 50, 175, 87, 40, 206, 53, 208, 220, 148, 13,
            ],
            [
                70, 240, 79, 112, 54, 157, 228, 146, 74, 122, 216, 88, 232, 62, 158, 13, 14, 146,
                115, 117, 176, 222, 90, 225, 244, 23, 94, 190, 150, 7, 136, 96,
            ],
            [
                22, 71, 241, 103, 45, 193, 195, 144, 183, 101, 154, 50, 39, 68, 49, 110, 51, 44,
                62, 0, 229, 113, 72, 81, 168, 29, 73, 106, 102, 40, 132, 24,
            ],
            [
                196, 133, 107, 11, 130, 105, 74, 33, 204, 171, 133, 221, 174, 193, 241, 36, 38,
                179, 196, 107, 219, 185, 181, 253, 228, 47, 155, 42, 231, 73, 41, 78,
            ],
            [
                58, 255, 225, 197, 115, 208, 160, 143, 39, 197, 82, 69, 143, 235, 92, 170, 74, 40,
                57, 11, 171, 227, 26, 185, 217, 207, 90, 185, 197, 190, 35, 60,
            ],
            [
                88, 43, 92, 118, 223, 136, 105, 145, 238, 186, 115, 8, 214, 112, 153, 253, 38, 108,
                205, 230, 157, 130, 11, 66, 101, 85, 253, 110, 110, 14, 148, 112,
            ],
        ];

        for i in 0..16 {
            let mut cs = TestConstraintSystem::<Fe25519>::new();
            let t = Fe25519::from_repr(bytes[i]);
            assert!(bool::from(t.is_some()));
            let t = t.unwrap();
            let t_alloc = AllocatedNum::alloc(&mut cs.namespace(|| "alloc t"), || Ok(t)).unwrap();
            let point_alloc = AllocatedAffinePoint::map_to_curve(&mut cs.namespace(|| "map t to curve"), t_alloc).unwrap();
            
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 541);
            
            let point = AffinePoint{
                x: point_alloc.x.get_value().unwrap(),
                y: point_alloc.y.get_value().unwrap()
            };
            assert_eq!(point.compress(), out[i]);
        }
    }

    #[test]
    fn test_elligator_circuit() {
    
        // These inputs are from
        // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#appendix-A.3
        let test_vectors: &[([u8; 64], [u8;32])] = &[
            (
                [
                    0x5d, 0x1b, 0xe0, 0x9e, 0x3d, 0x0c, 0x82, 0xfc, 0x53, 0x81, 0x12, 0x49, 0x0e,
                    0x35, 0x70, 0x19, 0x79, 0xd9, 0x9e, 0x06, 0xca, 0x3e, 0x2b, 0x5b, 0x54, 0xbf,
                    0xfe, 0x8b, 0x4d, 0xc7, 0x72, 0xc1, 0x4d, 0x98, 0xb6, 0x96, 0xa1, 0xbb, 0xfb,
                    0x5c, 0xa3, 0x2c, 0x43, 0x6c, 0xc6, 0x1c, 0x16, 0x56, 0x37, 0x90, 0x30, 0x6c,
                    0x79, 0xea, 0xca, 0x77, 0x05, 0x66, 0x8b, 0x47, 0xdf, 0xfe, 0x5b, 0xb6,
                ],
                [
                    0x30, 0x66, 0xf8, 0x2a, 0x1a, 0x74, 0x7d, 0x45, 0x12, 0x0d, 0x17, 0x40, 0xf1,
                    0x43, 0x58, 0x53, 0x1a, 0x8f, 0x04, 0xbb, 0xff, 0xe6, 0xa8, 0x19, 0xf8, 0x6d,
                    0xfe, 0x50, 0xf4, 0x4a, 0x0a, 0x46,
                ]
            ),
            (
                [
                    0xf1, 0x16, 0xb3, 0x4b, 0x8f, 0x17, 0xce, 0xb5, 0x6e, 0x87, 0x32, 0xa6, 0x0d,
                    0x91, 0x3d, 0xd1, 0x0c, 0xce, 0x47, 0xa6, 0xd5, 0x3b, 0xee, 0x92, 0x04, 0xbe,
                    0x8b, 0x44, 0xf6, 0x67, 0x8b, 0x27, 0x01, 0x02, 0xa5, 0x69, 0x02, 0xe2, 0x48,
                    0x8c, 0x46, 0x12, 0x0e, 0x92, 0x76, 0xcf, 0xe5, 0x46, 0x38, 0x28, 0x6b, 0x9e,
                    0x4b, 0x3c, 0xdb, 0x47, 0x0b, 0x54, 0x2d, 0x46, 0xc2, 0x06, 0x8d, 0x38,
                ],
                [
                    0xf2, 0x6e, 0x5b, 0x6f, 0x7d, 0x36, 0x2d, 0x2d, 0x2a, 0x94, 0xc5, 0xd0, 0xe7,
                    0x60, 0x2c, 0xb4, 0x77, 0x3c, 0x95, 0xa2, 0xe5, 0xc3, 0x1a, 0x64, 0xf1, 0x33,
                    0x18, 0x9f, 0xa7, 0x6e, 0xd6, 0x1b,
                ]
            ),
            (
                [
                    0x84, 0x22, 0xe1, 0xbb, 0xda, 0xab, 0x52, 0x93, 0x8b, 0x81, 0xfd, 0x60, 0x2e,
                    0xff, 0xb6, 0xf8, 0x91, 0x10, 0xe1, 0xe5, 0x72, 0x08, 0xad, 0x12, 0xd9, 0xad,
                    0x76, 0x7e, 0x2e, 0x25, 0x51, 0x0c, 0x27, 0x14, 0x07, 0x75, 0xf9, 0x33, 0x70,
                    0x88, 0xb9, 0x82, 0xd8, 0x3d, 0x7f, 0xcf, 0x0b, 0x2f, 0xa1, 0xed, 0xff, 0xe5,
                    0x19, 0x52, 0xcb, 0xe7, 0x36, 0x5e, 0x95, 0xc8, 0x6e, 0xaf, 0x32, 0x5c,
                ],
                [
                    0x00, 0x6c, 0xcd, 0x2a, 0x9e, 0x68, 0x67, 0xe6, 0xa2, 0xc5, 0xce, 0xa8, 0x3d,
                    0x33, 0x02, 0xcc, 0x9d, 0xe1, 0x28, 0xdd, 0x2a, 0x9a, 0x57, 0xdd, 0x8e, 0xe7,
                    0xb9, 0xd7, 0xff, 0xe0, 0x28, 0x26,
                ]
            ),
            (
                [
                    0xac, 0x22, 0x41, 0x51, 0x29, 0xb6, 0x14, 0x27, 0xbf, 0x46, 0x4e, 0x17, 0xba,
                    0xee, 0x8d, 0xb6, 0x59, 0x40, 0xc2, 0x33, 0xb9, 0x8a, 0xfc, 0xe8, 0xd1, 0x7c,
                    0x57, 0xbe, 0xeb, 0x78, 0x76, 0xc2, 0x15, 0x0d, 0x15, 0xaf, 0x1c, 0xb1, 0xfb,
                    0x82, 0x4b, 0xbd, 0x14, 0x95, 0x5f, 0x2b, 0x57, 0xd0, 0x8d, 0x38, 0x8a, 0xab,
                    0x43, 0x1a, 0x39, 0x1c, 0xfc, 0x33, 0xd5, 0xba, 0xfb, 0x5d, 0xbb, 0xaf,
                ],
                [
                    0xf8, 0xf0, 0xc8, 0x7c, 0xf2, 0x37, 0x95, 0x3c, 0x58, 0x90, 0xae, 0xc3, 0x99,
                    0x81, 0x69, 0x00, 0x5d, 0xae, 0x3e, 0xca, 0x1f, 0xbb, 0x04, 0x54, 0x8c, 0x63,
                    0x59, 0x53, 0xc8, 0x17, 0xf9, 0x2a,
                ]
            ),
            (
                [
                    0x16, 0x5d, 0x69, 0x7a, 0x1e, 0xf3, 0xd5, 0xcf, 0x3c, 0x38, 0x56, 0x5b, 0xee,
                    0xfc, 0xf8, 0x8c, 0x0f, 0x28, 0x2b, 0x8e, 0x7d, 0xbd, 0x28, 0x54, 0x4c, 0x48,
                    0x34, 0x32, 0xf1, 0xce, 0xc7, 0x67, 0x5d, 0xeb, 0xea, 0x8e, 0xbb, 0x4e, 0x5f,
                    0xe7, 0xd6, 0xf6, 0xe5, 0xdb, 0x15, 0xf1, 0x55, 0x87, 0xac, 0x4d, 0x4d, 0x4a,
                    0x1d, 0xe7, 0x19, 0x1e, 0x0c, 0x1c, 0xa6, 0x66, 0x4a, 0xbc, 0xc4, 0x13,
                ],
                [
                    0xae, 0x81, 0xe7, 0xde, 0xdf, 0x20, 0xa4, 0x97, 0xe1, 0x0c, 0x30, 0x4a, 0x76,
                    0x5c, 0x17, 0x67, 0xa4, 0x2d, 0x6e, 0x06, 0x02, 0x97, 0x58, 0xd2, 0xd7, 0xe8,
                    0xef, 0x7c, 0xc4, 0xc4, 0x11, 0x79,
                ]
            ),
            (
                [
                    0xa8, 0x36, 0xe6, 0xc9, 0xa9, 0xca, 0x9f, 0x1e, 0x8d, 0x48, 0x62, 0x73, 0xad,
                    0x56, 0xa7, 0x8c, 0x70, 0xcf, 0x18, 0xf0, 0xce, 0x10, 0xab, 0xb1, 0xc7, 0x17,
                    0x2d, 0xdd, 0x60, 0x5d, 0x7f, 0xd2, 0x97, 0x98, 0x54, 0xf4, 0x7a, 0xe1, 0xcc,
                    0xf2, 0x04, 0xa3, 0x31, 0x02, 0x09, 0x5b, 0x42, 0x00, 0xe5, 0xbe, 0xfc, 0x04,
                    0x65, 0xac, 0xcc, 0x26, 0x31, 0x75, 0x48, 0x5f, 0x0e, 0x17, 0xea, 0x5c,
                ],
                [
                    0xe2, 0x70, 0x56, 0x52, 0xff, 0x9f, 0x5e, 0x44, 0xd3, 0xe8, 0x41, 0xbf, 0x1c,
                    0x25, 0x1c, 0xf7, 0xdd, 0xdb, 0x77, 0xd1, 0x40, 0x87, 0x0d, 0x1a, 0xb2, 0xed,
                    0x64, 0xf1, 0xa9, 0xce, 0x86, 0x28,
                ]
            ),
            (
                [
                    0x2c, 0xdc, 0x11, 0xea, 0xeb, 0x95, 0xda, 0xf0, 0x11, 0x89, 0x41, 0x7c, 0xdd,
                    0xdb, 0xf9, 0x59, 0x52, 0x99, 0x3a, 0xa9, 0xcb, 0x9c, 0x64, 0x0e, 0xb5, 0x05,
                    0x8d, 0x09, 0x70, 0x2c, 0x74, 0x62, 0x2c, 0x99, 0x65, 0xa6, 0x97, 0xa3, 0xb3,
                    0x45, 0xec, 0x24, 0xee, 0x56, 0x33, 0x5b, 0x55, 0x6e, 0x67, 0x7b, 0x30, 0xe6,
                    0xf9, 0x0a, 0xc7, 0x7d, 0x78, 0x10, 0x64, 0xf8, 0x66, 0xa3, 0xc9, 0x82,
                ],
                [
                    0x80, 0xbd, 0x07, 0x26, 0x25, 0x11, 0xcd, 0xde, 0x48, 0x63, 0xf8, 0xa7, 0x43,
                    0x4c, 0xef, 0x69, 0x67, 0x50, 0x68, 0x1c, 0xb9, 0x51, 0x0e, 0xea, 0x55, 0x70,
                    0x88, 0xf7, 0x6d, 0x9e, 0x50, 0x65,
                ]
            ),
            (
                [
                    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                ],
                [
                    0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
                    0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
                    0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
                ]
            ),
            (
                [
                    0xed, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                ],
                [
                    0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
                    0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
                    0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
                ]
            ),
            (
                [
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
                ],
                [
                    0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
                    0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
                    0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
                ]
            ),
            (
                [
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80,
                ],
                [
                    0x30, 0x42, 0x82, 0x79, 0x10, 0x23, 0xb7, 0x31, 0x28, 0xd2, 0x77, 0xbd, 0xcb,
                    0x5c, 0x77, 0x46, 0xef, 0x2e, 0xac, 0x08, 0xdd, 0xe9, 0xf2, 0x98, 0x33, 0x79,
                    0xcb, 0x8e, 0x5e, 0xf0, 0x51, 0x7f,
                ]
            ),
        ];

        for (input, output) in test_vectors {
            let mut cs = TestConstraintSystem::<Fe25519>::new();
            let q_alloc = AllocatedAffinePoint::elligator2(&mut cs.namespace(|| "elligator map"), input).unwrap();
            let q = AffinePoint{
                x: q_alloc.x.get_value().unwrap(),
                y: q_alloc.y.get_value().unwrap()
            };
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 1089);
            assert_eq!(&q.compress(), output);
        }
    }
}