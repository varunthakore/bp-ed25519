use std::ops::{Add, Sub, Mul, Rem};
use bellperson::{ConstraintSystem, SynthesisError, LinearCombination, Variable};
use ff::{PrimeField, PrimeFieldBits};
use num_bigint::BigUint;
use num_traits::Zero;

use crate::{nonnative::vanilla::LimbedInt, curve::{AffinePoint, D}};

use super::vanilla::LimbedAffinePoint;


fn mul_lc_with_scalar<F>(
    lc: LinearCombination<F>,
    scalar: F
) -> LinearCombination<F>
where
    F: PrimeField
{
    let mut scaled_lc = LinearCombination::<F>::zero();
    for (var, coeff) in lc.iter() {
        scaled_lc = scaled_lc + (scalar*coeff, var);
    }
    scaled_lc
}

#[derive(Debug, Clone)]
pub struct AllocatedLimbedInt<F: PrimeField + PrimeFieldBits>
{
    // Modelling limbs as linear combinations is more flexible than
    // modelling them as AllocatedNums. For example, adding will not require
    // allocation of a new AllocatedNum
    limbs: Vec<LinearCombination<F>>,
    value: Option<LimbedInt<F>>,
}

impl<F> Add<&AllocatedLimbedInt<F>> for AllocatedLimbedInt<F>
where
    F: PrimeField + PrimeFieldBits 
 {
    type Output = Self;

    fn add(self, rhs: &AllocatedLimbedInt<F>) -> Self::Output {
        assert!(self.value.is_some());
        assert!(rhs.value.is_some());
        let self_value = self.clone().value.unwrap();
        let rhs_value = rhs.clone().value.unwrap();
        let self_len = self_value.len();
        let rhs_len = rhs_value.len();
        assert_eq!(self.limbs.len(), self_len);
        assert_eq!(rhs.limbs.len(), rhs_len);

        let sum_len = self_len.max(rhs_len);
        let mut sum = Self { 
            limbs: vec![LinearCombination::zero(); sum_len],
            value: Some(self_value + rhs_value),
        };
        for i in 0..sum_len {
            let mut tmp = LinearCombination::<F>::zero();
            if i < self_len {
                tmp = self.limbs[i].clone();
            }
            if i < rhs_len {
                tmp = tmp + &rhs.limbs[i];
            }
            sum.limbs[i] = tmp;
        }
        sum
    }
}

impl<F> Sub<&AllocatedLimbedInt<F>> for AllocatedLimbedInt<F>
where
    F: PrimeField + PrimeFieldBits 
 {
    type Output = Self;

    fn sub(self, rhs: &AllocatedLimbedInt<F>) -> Self::Output {
        assert!(self.value.is_some());
        assert!(rhs.value.is_some());
        let self_value = self.clone().value.unwrap();
        let rhs_value = rhs.clone().value.unwrap();
        let self_len = self_value.len();
        let rhs_len = rhs_value.len();
        assert_eq!(self.limbs.len(), self_len);
        assert_eq!(rhs.limbs.len(), rhs_len);

        let diff_len = self_len.max(rhs_len);
        let mut diff = Self { 
            limbs: vec![LinearCombination::zero(); diff_len],
            value: Some(self_value - rhs_value),
        };
        for i in 0..diff_len {
            let mut tmp = LinearCombination::<F>::zero();
            if i < self_len {
                tmp = self.limbs[i].clone();
            }
            if i < rhs_len {
                tmp = tmp - &rhs.limbs[i];
            }
            diff.limbs[i] = tmp;
        }
        diff
    }
}

impl<F> Mul<&LimbedInt<F>> for AllocatedLimbedInt<F>
where
    F: PrimeField + PrimeFieldBits
{
    type Output = Self;

    fn mul(self, rhs: &LimbedInt<F>) -> Self::Output {
        assert!(self.value.is_some());
        let self_value = self.clone().value.unwrap();
        let self_lc_vec = self.limbs;
        assert_eq!(self_lc_vec.len(), self_value.len());
        let prod_len = self_value.len() + rhs.len() - 1;

        let mut prod_lcs = vec![LinearCombination::<F>::zero(); prod_len];
        for i in 0..self_value.len() {
            for j in 0..rhs.len() {
                prod_lcs[i+j] = prod_lcs[i+j].clone() + &mul_lc_with_scalar(self_lc_vec[i].clone(), rhs.limbs[j]);
            }
        }
        Self {
            limbs: prod_lcs,
            value: Some(LimbedInt::<F>::calc_quadratic_limbs(&self_value, rhs)),
        }
    }
}
pub enum AllocatedOrConstantLimbedInt<F>
where
    F: PrimeField + PrimeFieldBits
{
    Allocated(AllocatedLimbedInt<F>),
    Constant(LimbedInt<F>)
}

impl<F> AllocatedLimbedInt<F>
where
    F: PrimeField + PrimeFieldBits
{
    pub fn alloc_from_limbed_int<CS>(
        cs: &mut CS,
        value: LimbedInt<F>,
        num_limbs: usize,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        if value.len() != num_limbs {
            return Err(SynthesisError::Unsatisfiable);
        }
        let limbs = (0..value.len())
            .map( |i| {
                cs.alloc(
                    || format!("limb {i}"),
                    || Ok(value.limbs[i])
                )
                .map(|v| LinearCombination::<F>::zero() + v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        
        Ok(AllocatedLimbedInt { limbs, value: Some(value) })
    }

    pub fn add_limbed_int<CS>(
        &self,
        limbed_int: &LimbedInt<F>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        assert!(self.value.is_some());
        let self_value = self.clone().value.unwrap();
        let self_lc_vec = self.limbs.clone();
        assert_eq!(self_lc_vec.len(), self_value.len());
        let sum_len = self_value.len().max(limbed_int.len());

        let mut sum_lcs = vec![LinearCombination::<F>::zero(); sum_len];
        let mut sum_values = LimbedInt::<F>::default();
        for i in 0..sum_len {
            let mut tmp = LinearCombination::<F>::zero();
            let mut tmp_val = F::zero();
            if i < self_value.len() {
                tmp = self_lc_vec[i].clone();
                tmp_val = self_value.limbs[i];
            }
            if i < limbed_int.len() {
                tmp = tmp + &LinearCombination::<F>::from_coeff(CS::one(), limbed_int.limbs[i]);
                tmp_val = tmp_val + limbed_int.limbs[i];
            }
            sum_lcs[i] = tmp;
            sum_values.limbs[i] = tmp_val;
        }

        Ok(Self {
            limbs: sum_lcs,
            value: Some(sum_values),
        })
    }

    pub fn alloc_product<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<AllocatedLimbedInt<F>, SynthesisError> {
        if self.value.is_none() || other.value.is_none() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let a_l = self.clone().value.unwrap();
        let b_l = other.clone().value.unwrap();
        if self.limbs.len() != a_l.len() || other.limbs.len() != b_l.len() {
            return Err(SynthesisError::Unsatisfiable);
        } 

        let prod = LimbedInt::<F>::calc_quadratic_limbs(&a_l, &b_l);
        let prod_limbs = (0..prod.len())
            .map(|i| {
                cs.alloc(
                    || format!("product limb {i}"),
                    || Ok(prod.limbs[i]),
                )
                .map(|v| LinearCombination::<F>::zero() + v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let product = AllocatedLimbedInt {
            limbs: prod_limbs,
            value: Some(prod),
        };

        let mut x = F::zero();
        for _ in 0..product.limbs.len() {
            x += F::one();
            cs.enforce(
                || format!("pointwise product @ {x:?}"),
                |lc| {
                    let mut i = F::one();
                    self.limbs.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i *= x;
                        r
                    })
                },
                |lc| {
                    let mut i = F::one();
                    other.limbs.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i *= x;
                        r
                    })
                },
                |lc| {
                    let mut i = F::one();
                    product.limbs.iter().fold(lc, |lc, c| {
                        let r = lc + (i, c);
                        i *= x;
                        r
                    })
                },
            )
        }
        
        Ok(product)
    }
    
    pub fn alloc_cubic_product_3var<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        b: &Self,
        c: &Self,
    ) -> Result<AllocatedLimbedInt<F>, SynthesisError> {
        if self.value.is_none() || b.value.is_none() || c.value.is_none() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let a_l = self.clone().value.unwrap();
        let b_l = b.clone().value.unwrap();
        let c_l = c.clone().value.unwrap();
        if self.limbs.len() != a_l.len()
            || b_l.limbs.len() != b_l.len()
            || c_l.limbs.len() != c_l.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let ab = self.alloc_product(
            &mut cs.namespace(|| "a times b"),
            &b
        )?;
        let abc = ab.alloc_product(
            &mut cs.namespace(|| "ab times c"),
            &c
        );
        abc
    }

    pub fn alloc_cubic_product_2var1const<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        b: &Self,
        c: &LimbedInt<F>,
    ) -> Result<AllocatedLimbedInt<F>, SynthesisError> {
        if self.value.is_none() || b.value.is_none() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let a_l = self.clone().value.unwrap();
        let b_l = b.clone().value.unwrap();
        if self.limbs.len() != a_l.len()
            || b_l.limbs.len() != b_l.len()
            || c.limbs.len() != c.len() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let ab = self.alloc_product(
            &mut cs.namespace(|| "a times b"),
            &b
        )?;
        let abc = ab * c;
        Ok(abc)
    }

    pub fn fold_quadratic_limbs(
        &self,
    ) -> Result<AllocatedLimbedInt<F>, SynthesisError> {
        if self.value.is_none() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let f = self.clone().value.unwrap();
        if self.limbs.len() != f.len() || f.len() != 7 {
            return Err(SynthesisError::Unsatisfiable);
        }

        let c1 = F::from(38u64);

        let f_limbs = self.clone().limbs; 
        let mut h_limbs = vec![LinearCombination::<F>::zero(); 4];
        h_limbs[0] = f_limbs[0].clone() + &mul_lc_with_scalar(f_limbs[4].clone(), c1);
        h_limbs[1] = f_limbs[1].clone() + &mul_lc_with_scalar(f_limbs[5].clone(), c1);
        h_limbs[2] = f_limbs[2].clone() + &mul_lc_with_scalar(f_limbs[6].clone(), c1);
        h_limbs[3] = f_limbs[3].clone();

        Ok(AllocatedLimbedInt {
            limbs: h_limbs,
            value: Some(LimbedInt::fold_quadratic_limbs(&f)),
        })
    }

    pub fn fold_cubic_limbs(
        &self,
    ) -> Result<Self, SynthesisError> {
        if self.value.is_none() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let g = self.clone().value.unwrap();
        if self.limbs.len() != g.len() || g.len() != 10 {
            return Err(SynthesisError::Unsatisfiable);
        }

        let c1 = F::from(38u64);
        let c2 = F::from(1444u64);

        let g_limbs = self.clone().limbs; 
        let mut h_limbs = vec![LinearCombination::<F>::zero(); 4];
        h_limbs[0] = g_limbs[0].clone() + &mul_lc_with_scalar(g_limbs[4].clone(), c1)
            + &mul_lc_with_scalar(g_limbs[8].clone(), c2);
        h_limbs[1] = g_limbs[1].clone() + &mul_lc_with_scalar(g_limbs[5].clone(), c1)
            + &mul_lc_with_scalar(g_limbs[9].clone(), c2);
        h_limbs[2] = g_limbs[2].clone() + &mul_lc_with_scalar(g_limbs[6].clone(), c1);
        h_limbs[3] = g_limbs[3].clone() + &mul_lc_with_scalar(g_limbs[7].clone(), c1);

        Ok(AllocatedLimbedInt {
            limbs: h_limbs,
            value: Some(LimbedInt::fold_cubic_limbs(&g)),
        })
    }

    pub fn check_difference_is_zero<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        let diff = self - other;
        if diff.value.is_none() {
            return Err(SynthesisError::Unsatisfiable);
        }
        let diff_value = diff.value.unwrap();
        let diff_len = diff.limbs.len();
        let mut carries: Vec<F> = vec![F::zero(); diff_len-1];
        let mut carry_variables: Vec<Variable> = vec![];
        let exp64 = BigUint::from(64u64);
        let base = F::from(2u64).pow_vartime(exp64.to_u64_digits());

        for i in 0..diff_len-1 {
            if i == 0 {
                let limb_bits = diff_value.limbs[0].to_le_bits();
                let mut coeff = F::one();
                // Calculating carries[0] as diff_value.limbs[0] shifted to the right 64 times (discard the 64 LSBs)
                for (j, bit) in limb_bits.into_iter().enumerate() {
                    if  j >= 64 {
                        if bit {
                            carries[0] += coeff;
                        }
                        coeff += coeff;
                    }
                }
                assert_eq!(diff_value.limbs[0], carries[0]*base);

                let cv = cs.alloc(
                    || format!("carry {i}"),
                    || Ok(carries[i])
                );
                assert!(cv.is_ok());
                carry_variables.push(cv.unwrap());

                cs.enforce(
                    || format!("Enforce carry constraint {i}"),
                    |lc| lc + &LinearCombination::from_coeff(carry_variables[i], base),
                    |lc| lc + CS::one(),
                    |lc| lc + &diff.limbs[i],
                );
            }
            else {
                let limb_bits = (carries[i-1] + diff_value.limbs[i]).to_le_bits();
                let mut coeff = F::one();
                // Calculating carries[i] as diff_value.limbs[i] + carries[i-1] shifted to the right 64 times (discard the 64 LSBs)
                for (j, bit) in limb_bits.into_iter().enumerate() {
                    if  j >= 64 {
                        if bit {
                            carries[i] += coeff;
                        }
                        coeff += coeff;
                    }
                }
                assert_eq!(diff_value.limbs[i] + carries[i-1], carries[i]*base);

                let cv = cs.alloc(
                    || format!("carry {i}"),
                    || Ok(carries[i])
                );
                assert!(cv.is_ok());
                carry_variables.push(cv.unwrap());

                cs.enforce(
                    || format!("Enforce carry constraint {i}"),
                    |lc| lc + &LinearCombination::from_coeff(carry_variables[i], base),
                    |lc| lc + CS::one(),
                    |lc| lc + &(diff.limbs[i].clone() + carry_variables[i-1]),
                );
            }
        }
        assert_eq!(diff_value.limbs[diff_len-1] + carries[diff_len-2], F::zero());
        Ok(cs.enforce(
            || format!("Enforce final zero"),
            |lc| lc + &diff.limbs[diff_len-1] + carry_variables[diff_len-2],
            |lc| lc + CS::one(),
            |lc| lc,
        ))
    }

    pub fn reduce_cubic_product<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        c: &AllocatedOrConstantLimbedInt<F>,
    ) -> Result<Self, SynthesisError> {

        let abc = match c {
            AllocatedOrConstantLimbedInt::Allocated(allocated_c) => a.alloc_cubic_product_3var(
                &mut cs.namespace(|| format!("allocate unreduced cubic product")),
                b,
                allocated_c,
            ).unwrap(),
            AllocatedOrConstantLimbedInt::Constant(constant_c) => a.alloc_cubic_product_2var1const(
                &mut cs.namespace(|| format!("allocate unreduced cubic product")),
                b,
                constant_c,
            ).unwrap(),
        };
        let a_l = a.clone().value.unwrap();
        let b_l = b.clone().value.unwrap();
        let c_l = match c {
            AllocatedOrConstantLimbedInt::Allocated(allocated_c) => allocated_c.clone().value.unwrap(),
            AllocatedOrConstantLimbedInt::Constant(constant_c) => constant_c.clone(),
        };

        let one = BigUint::from(1u64);
        let q: BigUint = (one.clone() << 255) - BigUint::from(19u64);
        let q_l = LimbedInt::<F>::from(&q);
        
        let (t_l, r_l) = LimbedInt::<F>::calc_cubic_product_witness(
            &a_l,
            &b_l,
            &c_l,
        );
        let t = Self::alloc_from_limbed_int(
            &mut cs.namespace(|| "cubic product quotient"),
            t_l,
            3
        )?;

        let r = Self::alloc_from_limbed_int(
            &mut cs.namespace(|| "cubic product remainder"),
            r_l,
            4
        )?;

        let tq = t * &q_l;
        let tq_plus_r = tq + &r;
        let h_l = abc.fold_cubic_limbs().unwrap();

        h_l.check_difference_is_zero(
            &mut cs.namespace(|| "checking difference is zero"),
            &tq_plus_r
        )?;
        Ok(r)
    }

    pub fn verify_x_coordinate_quadratic_is_zero<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        x1: &Self,
        x2: &Self,
        y1: &Self,
        y2: &Self,
        x3: &Self,
        v: &Self,
    ) -> Result<(), SynthesisError> {
        let one = BigUint::from(1u64);
        let q_uint: BigUint = (one.clone() << 255) - BigUint::from(19u64);
        let q_l = LimbedInt::<F>::from(&q_uint);
        let mut q70_l = LimbedInt::<F>::default();
        let two = F::from(2u64);
        let two_power_70 = two.pow_vartime(&[70u64]);
        for i in 0..q_l.len() {
            q70_l.limbs[i] = q_l.limbs[i] * two_power_70;
        }

        let x1y2 = x1.alloc_product(
            &mut cs.namespace(|| "alloc x1*y2"),
            y2,
        )?;
        let x1y2_folded = x1y2.fold_quadratic_limbs()?;
        let x2y1 = x2.alloc_product(
            &mut cs.namespace(|| "alloc x2*y1"),
            y1,
        )?;
        let x2y1_folded = x2y1.fold_quadratic_limbs()?;
        let x3v = x3.alloc_product(
            &mut cs.namespace(|| "alloc x3*v"),
            v,
        )?;
        let x3v_folded = x3v.fold_quadratic_limbs()?;

        let mut g_al = x1y2_folded + &x2y1_folded - &x3v_folded - x3;
        g_al = g_al.add_limbed_int::<CS>(&q70_l)?;
        
        let g_uint = BigUint::from(&g_al.clone().value.unwrap());
        assert!(g_uint.clone().rem(q_uint.clone()).is_zero());
        let t_uint = g_uint.clone() / q_uint.clone();
        assert!(t_uint < (one << 72));
        assert!(g_uint == t_uint.clone()*q_uint.clone());
        
        let t_l = LimbedInt::<F>::from(&t_uint);
        let t_al = Self::alloc_from_limbed_int(
            &mut cs.namespace(|| "allocate quotient t"),
            t_l,
            2,
        )?;
        let tq_al = t_al * &q_l;

        g_al.check_difference_is_zero(
            &mut cs.namespace(|| "checking difference is zero"),
            &tq_al,
        )
    }

    pub fn verify_y_coordinate_quadratic_is_zero<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        x1: &Self,
        x2: &Self,
        y1: &Self,
        y2: &Self,
        y3: &Self,
        v: &Self,
    ) -> Result<(), SynthesisError> {
        let one = BigUint::from(1u64);
        let q_uint: BigUint = (one.clone() << 255) - BigUint::from(19u64);
        let q_l = LimbedInt::<F>::from(&q_uint);
        let mut q70_l = LimbedInt::<F>::default();
        let two = F::from(2u64);
        let two_power_70 = two.pow_vartime(&[70u64]);
        for i in 0..q_l.len() {
            q70_l.limbs[i] = q_l.limbs[i] * two_power_70;
        }

        let x1x2 = x1.alloc_product(
            &mut cs.namespace(|| "alloc x1*x2"),
            x2,
        )?;
        let x1x2_folded = x1x2.fold_quadratic_limbs()?;
        let y1y2 = y1.alloc_product(
            &mut cs.namespace(|| "alloc y1*y2"),
            y2,
        )?;
        let y1y2_folded = y1y2.fold_quadratic_limbs()?;
        let y3v = y3.alloc_product(
            &mut cs.namespace(|| "alloc y3*v"),
            v,
        )?;
        let y3v_folded = y3v.fold_quadratic_limbs()?;

        let mut g_al = x1x2_folded + &y1y2_folded + &y3v_folded - y3;
        g_al = g_al.add_limbed_int::<CS>(&q70_l)?;
        
        let g_uint = BigUint::from(&g_al.clone().value.unwrap());
        assert!(g_uint.clone().rem(q_uint.clone()).is_zero());
        let t_uint = g_uint.clone() / q_uint.clone();
        assert!(t_uint < (one << 72));
        assert!(g_uint == t_uint.clone()*q_uint.clone());
        
        let t_l = LimbedInt::<F>::from(&t_uint);
        let t_al = Self::alloc_from_limbed_int(
            &mut cs.namespace(|| "allocate quotient t"),
            t_l,
            2,
        )?;
        let tq_al = t_al * &q_l;

        g_al.check_difference_is_zero(
            &mut cs.namespace(|| "checking difference is zero"),
            &tq_al,
        )
    }
}

#[derive(Debug, Clone)]
pub struct AllocatedAffinePoint<F: PrimeField + PrimeFieldBits> {
    x: AllocatedLimbedInt<F>,
    y: AllocatedLimbedInt<F>,
    value: AffinePoint,
}

impl<F: PrimeField + PrimeFieldBits> AllocatedAffinePoint<F>  {
    pub fn alloc_affine_point<CS>(
        cs: &mut CS,
        value: AffinePoint,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let limbed_affine_point = LimbedAffinePoint::<F>::from(&value);
        let x = AllocatedLimbedInt::<F>::alloc_from_limbed_int(
            &mut cs.namespace(|| "x coordinate"),
            limbed_affine_point.x,
            4
        )?;
        let y = AllocatedLimbedInt::<F>::alloc_from_limbed_int(
            &mut cs.namespace(|| "y coordinate"),
            limbed_affine_point.y,
            4
        )?;
        Ok(Self { x, y, value })
    }

    fn verify_ed25519_point_addition<CS>(
        cs: &mut CS,
        p: &Self,
        q: &Self,
        r: &Self,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let x1_l = &p.x;
        let y1_l = &p.y;
        let x2_l = &q.x;
        let y2_l = &q.y;
        let x3_l = &r.x;
        let y3_l = &r.y;

        let d_l = LimbedInt::<F>::from(&D);

        let u_l = AllocatedLimbedInt::reduce_cubic_product(
            &mut cs.namespace(|| "allocate d*x1*x2 mod q"),
            &x1_l,
            &x2_l,
            &AllocatedOrConstantLimbedInt::Constant(d_l),
        )?;
        
        let v_l = AllocatedLimbedInt::reduce_cubic_product(
            &mut cs.namespace(|| "allocate u*y1*y2 mod q"),
            &u_l,
            &y1_l,
            &AllocatedOrConstantLimbedInt::<F>::Allocated(y2_l.clone()),
        )?;
        
        
        AllocatedLimbedInt::<F>::verify_x_coordinate_quadratic_is_zero(
            &mut cs.namespace(|| "checking x coordinate quadratic"),
            x1_l, x2_l, y1_l, y2_l, x3_l, &v_l
        )?;
        AllocatedLimbedInt::<F>::verify_y_coordinate_quadratic_is_zero(
            &mut cs.namespace(|| "checking y coordinate quadratic"),
            x1_l, x2_l, y1_l, y2_l, y3_l, &v_l
        )?;
        Ok(())
    }
    
    pub fn ed25519_point_addition<CS>(
        cs: &mut CS,
        p: &Self,
        q: &Self,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let sum_value = p.value + q.value;
        let sum = Self::alloc_affine_point(
            &mut cs.namespace(|| "allocate sum"),
            sum_value,
        )?;

        Self::verify_ed25519_point_addition(
            &mut cs.namespace(|| "verify point addition"),
            p,
            q,
            &sum,
        )?;

        Ok(sum)
    }

}

#[cfg(test)]
mod tests {
    use crate::curve::Ed25519Curve;

    use super::*;
    use bellperson::gadgets::test::TestConstraintSystem;
    use crypto_bigint::{U256, Random};
    use num_traits::Zero;
    use pasta_curves::Fp;
    use num_bigint::{RandBigInt, BigUint};

    #[test]
    fn alloc_limbed_sum() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_uint = rng.gen_biguint(255u64);
        let b_uint = rng.gen_biguint(255u64);
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);

        let a = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc a"),
            a_l,
            4
        );
        assert!(a.is_ok());
        let b = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc b"),
            b_l,
            4
        );
        assert!(b.is_ok());

        let a = a.unwrap();
        let b = b.unwrap();
        let sum = a.clone() + &b;

        for i in 0..sum.limbs.len() {
            cs.enforce(
                || format!("sum {i}"),
                |lc| lc + &a.limbs[i] + &b.limbs[i],
                |lc| lc + TestConstraintSystem::<Fp>::one(),
                |lc| lc + &sum.limbs[i],
            );
        }
        
        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());
    }

    #[test]
    fn alloc_limbed_difference() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let x_uint = rng.gen_biguint(255u64);
        let y_uint = rng.gen_biguint(255u64);
        let (a_uint, b_uint) = if x_uint > y_uint {
            (x_uint, y_uint)
        } else {
            (y_uint, x_uint)
        };
        let diff_uint = a_uint.clone() - b_uint.clone();
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);
        let diff = LimbedInt::<Fp>::from(&diff_uint);
        println!("{:?}\n{:?}", diff_uint, BigUint::from(&diff));

        let a = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc a"),
            a_l,
            4
        );
        assert!(a.is_ok());
        let b = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc b"),
            b_l,
            4
        );
        assert!(b.is_ok());

        let a = a.unwrap();
        let b = b.unwrap();
        let diff = a.clone() - &b;
        let a_val = a.value.unwrap();
        let b_val = b.value.unwrap();
        let diff_val = diff.value.unwrap();

        for i in 0..diff.limbs.len() {
            assert_eq!(a_val.limbs[i]-b_val.limbs[i], diff_val.limbs[i]);
            cs.enforce(
                || format!("sum {i}"),
                |lc| lc + &a.limbs[i] - &b.limbs[i],
                |lc| lc + TestConstraintSystem::<Fp>::one(),
                |lc| lc + &diff.limbs[i],
            );
        }
        
        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());
    }

    #[test]
    fn alloc_limbed_quadratic_product() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_uint = rng.gen_biguint(192u64);
        let b_uint = rng.gen_biguint(256u64);
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);

        let a = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc a"),
            a_l,
            3
        );
        assert!(a.is_ok());
        let b = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc b"),
            b_l,
            4
        );
        assert!(b.is_ok());
        
        let a = a.unwrap();
        let b = b.unwrap();

        let prod = a.alloc_product(
            &mut cs.namespace(|| "product"),
            &b
        );
        assert!(prod.is_ok());
        assert_eq!(BigUint::from(&prod.unwrap().value.unwrap()), a_uint*b_uint);

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_limbed_cubic_product() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_uint = rng.gen_biguint(256u64);
        let b_uint = rng.gen_biguint(256u64);
        let c_uint = rng.gen_biguint(256u64);
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);
        let c_l = LimbedInt::<Fp>::from(&c_uint);

        let a = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc a"),
            a_l,
            4
        );
        assert!(a.is_ok());
        let b = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc b"),
            b_l,
            4
        );
        assert!(b.is_ok());
        let c = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc c"),
            c_l,
            4
        );
        assert!(c.is_ok());
        
        let a = a.unwrap();
        let b = b.unwrap();
        let c = c.unwrap();

        let prod = a.alloc_cubic_product_3var(
            &mut cs.namespace(|| "product"),
            &b,
            &c,
        );
        assert!(prod.is_ok());
        assert_eq!(BigUint::from(&prod.unwrap().value.unwrap()), a_uint*b_uint*c_uint);

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_limbed_fold_quadratic() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_uint = rng.gen_biguint(256u64);
        let b_uint = rng.gen_biguint(256u64);
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);

        let a = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc a"),
            a_l,
            4
        );
        assert!(a.is_ok());
        let b = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc b"),
            b_l,
            4
        );
        assert!(b.is_ok());
        
        let a = a.unwrap();
        let b = b.unwrap();

        let prod = a.alloc_product(
            &mut cs.namespace(|| "product"),
            &b
        );
        assert!(prod.is_ok());

        let h = prod.unwrap().fold_quadratic_limbs().unwrap();
        assert!(h.value.is_some());
        let h_value = h.value.unwrap();
        let one = TestConstraintSystem::<Fp>::one();
        for i in 0..h_value.len() {
            cs.enforce(|| format!("limb {i} equality"),
                |lc| lc + &h.limbs[i],
                |lc| lc + one,
                |lc| lc + (h_value.limbs[i], one),
            );
        }


        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_limbed_fold_cubic() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_uint = rng.gen_biguint(256u64);
        let b_uint = rng.gen_biguint(256u64);
        let c_uint = rng.gen_biguint(256u64);
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);
        let c_l = LimbedInt::<Fp>::from(&c_uint);

        let a = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc a"),
            a_l,
            4
        );
        assert!(a.is_ok());
        let b = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc b"),
            b_l,
            4
        );
        assert!(b.is_ok());
        let c = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc c"),
            c_l,
            4
        );
        assert!(c.is_ok());
        
        
        let a = a.unwrap();
        let b = b.unwrap();
        let c = c.unwrap();

        let prod = a.alloc_cubic_product_3var(
            &mut cs.namespace(|| "product"),
            &b,
            &c,
        );
        assert!(prod.is_ok());

        let h = prod.unwrap().fold_cubic_limbs().unwrap();
        assert!(h.value.is_some());
        let h_value = h.value.unwrap();
        let one = TestConstraintSystem::<Fp>::one();
        for i in 0..h_value.len() {
            cs.enforce(|| format!("limb {i} equality"),
                |lc| lc + &h.limbs[i],
                |lc| lc + one,
                |lc| lc + (h_value.limbs[i], one),
            );
        }

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_limbed_check_difference() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_uint = rng.gen_biguint(256u64);
        let b_uint = rng.gen_biguint(256u64);
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);

        let ab_l = LimbedInt::<Fp>::calc_quadratic_limbs(&a_l, &b_l);
        let ab_folded_l = LimbedInt::<Fp>::fold_quadratic_limbs(&ab_l);
        let ab_folded_uint = BigUint::from(&ab_folded_l);

        let one = BigUint::from(1u64);
        let q_uint: BigUint = (one.clone() << 255) - BigUint::from(19u64);
        let r_uint = ab_folded_uint.clone() % q_uint.clone();
        let t_uint = (ab_folded_uint.clone() -r_uint.clone())/q_uint.clone();
        assert!(((ab_folded_uint - t_uint.clone()*q_uint.clone() - r_uint.clone()).is_zero()));

        let q_l = LimbedInt::<Fp>::from(&q_uint);
        let mut t_l = LimbedInt::<Fp>::from(&t_uint);
        t_l.pad_limbs(2);
        let r_l = LimbedInt::<Fp>::from(&r_uint);

        let ab_folded = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc ab_folded"),
            ab_folded_l,
            4
        );
        assert!(ab_folded.is_ok());
        let t = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc t"),
            t_l,
            2
        );
        assert!(t.is_ok());
        let r = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc r"),
            r_l,
            4
        );
        assert!(r.is_ok());
        
        let ab_folded = ab_folded.unwrap();
        let t = t.unwrap();
        let r = r.unwrap();

        let tq = t * &q_l;
        let tq_plus_r = tq + &r;

        let res = ab_folded.check_difference_is_zero(
            &mut cs.namespace(|| "check difference is zero"),
            &tq_plus_r
        );
        assert!(res.is_ok());

        
        println!("{:?}", cs.which_is_unsatisfied());
        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_limbed_reduce_cubic() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut rng = rand::thread_rng();
        let a_uint = rng.gen_biguint(256u64);
        let b_uint = rng.gen_biguint(256u64);
        let c_uint = rng.gen_biguint(256u64);
        let a_l = LimbedInt::<Fp>::from(&a_uint);
        let b_l = LimbedInt::<Fp>::from(&b_uint);
        let c_l = LimbedInt::<Fp>::from(&c_uint);
        let (_, r_l) = LimbedInt::<Fp>::calc_cubic_product_witness(&a_l, &b_l, &c_l);

        let a = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc a"),
            a_l,
            4
        );
        assert!(a.is_ok());
        let b = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc b"),
            b_l,
            4
        );
        assert!(b.is_ok());
        let c = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc c"),
            c_l,
            4
        );
        assert!(c.is_ok());
        let r = AllocatedLimbedInt::<Fp>::alloc_from_limbed_int(
            &mut cs.namespace(|| "alloc r"),
            r_l,
            4
        );
        assert!(r.is_ok());
        
        let a = a.unwrap();
        let b = b.unwrap();
        let c = c.unwrap();
        let r = r.unwrap();

        let r_calc = AllocatedLimbedInt::<Fp>::reduce_cubic_product(
            &mut cs.namespace(|| "verify cubic product reduced mod q"),
            &a,
            &b,
            &AllocatedOrConstantLimbedInt::Allocated(c),
        );
        assert!(r_calc.is_ok());
        let r_calc = r_calc.unwrap();

        let one = TestConstraintSystem::<Fp>::one();
        for i in 0..r.limbs.len() {
            cs.enforce(|| format!("r limb {i} equality"),
                |lc| lc + &r.limbs[i],
                |lc| lc + one,
                |lc| lc + &r_calc.limbs[i],
            );
        }

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }

    #[test]
    fn alloc_affine_point_addition_verification() {
        let b = Ed25519Curve::basepoint();
        let mut rng = rand::thread_rng();
        let scalar = U256::random(&mut rng);
        let p = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let scalar = U256::random(&mut rng);
        let q = Ed25519Curve::scalar_multiplication(&b, &scalar);
        let sum_expected_value = p.add(q);

        let mut cs = TestConstraintSystem::<Fp>::new();

        let p_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "alloc point p"),
            p,
        );
        assert!(p_alloc.is_ok());
        let p_al = p_alloc.unwrap();

        let q_alloc = AllocatedAffinePoint::alloc_affine_point(
            &mut cs.namespace(|| "alloc point q"),
            q,
        );
        assert!(q_alloc.is_ok());
        let q_al = q_alloc.unwrap();

        let sum_alloc = AllocatedAffinePoint::ed25519_point_addition(
            &mut cs.namespace(|| "adding p and q"),
            &p_al,
            &q_al,
        );
        assert!(sum_alloc.is_ok());
        let sum_al = sum_alloc.unwrap();

        assert_eq!(sum_expected_value, sum_al.value);

        assert!(cs.is_satisfied());
        println!("Num constraints = {:?}", cs.num_constraints());
        println!("Num inputs = {:?}", cs.num_inputs());

    }
}