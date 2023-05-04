use halo2_proofs::circuit::Value;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Error, Expression, Instance, Selector},
    poly::Rotation,
};

use crate::table::*;

/// This module assigns the GCD of two integers through Euclid's algorithm,
/// and assigns the LCM in another region. The GCD can be constrained to 1,
/// forcing (a, b) to be coprimes. Any results can be exposed in an instance
/// column.
///
// +-----------+----------+------------+----------+-------+-----------+-------+----------+
// | col_a     | col_b    | col_c      | q_euclid | q_gcd | q_coprime | q_lcm | q_lookup |
// +-----------+----------+------------+----------+-------+-----------+-------+----------+
// | a         | b        | a // b     | 0        | 0     | 0         | 0     | 1        |
// | b         | a%b      | b // (a%b) | 1        | 0     | 0         | 0     | 1        |
// | ...       | ...      | ...        | 1        | 0     | 0         | 0     | 1        |
// | gcd(a, b) | 0        | 0          | 1        | 1     | 0/1       | 0     | 1        |
// |           |          |            |          |       |           |       |          |
// | a         | b        |            | 0        | 0     | 0         | 1     | 0        |
// | gcd(a, b) | lcm(a,b) |            | 0        | 0     | 0         | 0     | 0        |
// +-----------+----------+------------+----------+-------+-----------+-------+----------+

#[derive(Debug, Clone)]
pub struct CoprimeConfig<F: FieldExt, const RANGE: usize> {
    a: Column<Advice>,
    b: Column<Advice>,

    exp: Column<Instance>,

    range_check: RangeTableConfig<F, RANGE>,

    q_range: Selector,
    q_euclid_init: Selector,
    q_euclid_ss: Selector,
    q_gcd: Selector,
    q_coprime: Selector,
    q_lcm: Selector,
}

impl<F: FieldExt, const RANGE: usize> CoprimeConfig<F, RANGE> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let a = meta.advice_column();
        let b = meta.advice_column();

        let exp = meta.instance_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(exp);

        let range_check = RangeTableConfig::<F, RANGE>::configure(meta);

        let q_lcm = meta.selector();
        let q_coprime = meta.selector();

        let q_euclid_init = meta.complex_selector();
        let q_euclid_ss = meta.complex_selector();
        let q_gcd = meta.complex_selector();
        let q_range = meta.complex_selector();

        // Verify that this is a valid Euclid's algorithm step
        // No overflows possible in the constraints as long as RANGE doesn't exceed p/2
        meta.create_gate("euclid's algorithm init", |meta| {
            let q_euclid_init = meta.query_selector(q_euclid_init);

            let a_prev = meta.query_advice(a, Rotation::prev());
            let b_prev = meta.query_advice(b, Rotation::prev());

            let a_cur = meta.query_advice(a, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur());

            Constraints::with_selector(
                q_euclid_init,
                [(
                    "a_prev == b_prev * a_cur + b_cur",
                    b_prev * a_cur + b_cur - a_prev,
                )],
            )
        });

        meta.create_gate("steady-state euclid's algorithm", |meta| {
            let q_euclid_ss = meta.query_selector(q_euclid_ss);

            let a_2prev = meta.query_advice(a, Rotation(-2));
            let b_2prev = meta.query_advice(b, Rotation(-2));

            let a_prev = meta.query_advice(a, Rotation::prev());
            let b_prev = meta.query_advice(b, Rotation::prev());

            let a_cur = meta.query_advice(a, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur());

            Constraints::with_selector(
                q_euclid_ss,
                [(
                    "b_2prev == b_prev * a_cur + b_cur",
                    b_prev * a_cur + b_cur - b_2prev,
                )],
            )
        });

        // Verify that the given row is a final state of a Euclid algorithm
        // Means only a is nonzero
        // MUST be used with q_euclid to check for valid transition
        meta.create_gate("gcd/coprime check", |meta| {
            let q_euclid_init = meta.query_selector(q_euclid_init);
            let q_euclid_ss = meta.query_selector(q_euclid_ss);
            let q_gcd = meta.query_selector(q_gcd);
            let q_coprime = meta.query_selector(q_coprime);

            let a_cur = meta.query_advice(a, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur()); // 0

            let a_prev = meta.query_advice(a, Rotation::prev());
            let b_prev = meta.query_advice(b, Rotation::prev()); // GCD

            vec![
                q_gcd.clone() * b_cur,                                           // b_cur = 0
                q_coprime.clone() * (b_prev - Expression::Constant(F::from(1))), // b_cur = GCD(a, b) = 1
                q_gcd.clone()
                    * (q_euclid_init - Expression::Constant(F::from(1)))
                    * (q_euclid_ss - Expression::Constant(F::from(1))), // q_gcd can only be 1 if either q_euclid_init or ss are 1
                q_coprime.clone() * (q_gcd - Expression::Constant(F::from(1))), // q_coprime can only be 1 if q_gcd is 1
            ]
        });

        // Verify that the provided LCM = a * b / GCD(a, b)
        // No overflows possible in the constraints as long as RANGE doesn't exceed p/2
        meta.create_gate("lcm check", |meta| {
            let q_lcm = meta.query_selector(q_lcm);

            let a_cur = meta.query_advice(a, Rotation::cur()); // a
            let b_cur = meta.query_advice(b, Rotation::cur()); // b

            let a_next = meta.query_advice(a, Rotation::next()); // GCD
            let b_next = meta.query_advice(b, Rotation::next()); // LCM

            Constraints::with_selector(
                q_lcm,
                [(
                    "lcm * gcd == a_cur * b_cur",
                    a_cur * b_cur - a_next * b_next,
                )],
            )
        });

        // Constrain all elements of current row to 0..RANGE
        meta.lookup(|meta| {
            let q_range = meta.query_selector(q_range);
            let a_cur = meta.query_advice(a, Rotation::cur());

            vec![(q_range * a_cur, range_check.value)]
        });

        meta.lookup(|meta| {
            let q_range = meta.query_selector(q_range);
            let b_cur = meta.query_advice(b, Rotation::cur());

            vec![(q_range * b_cur, range_check.value)]
        });

        CoprimeConfig {
            a,
            b,
            exp,
            range_check,
            q_range,
            q_euclid_init,
            q_euclid_ss,
            q_gcd,
            q_coprime,
            q_lcm,
        }
    }

    fn euclid_gcd_steps(mut a: u128, mut b: u128) -> Vec<(u128, u128)> {
        // Initialize with the Euclid-init state
        let mut result = vec![(a, b), (a / b, a % b)];

        // When the modulo (b) is zero that means the algorithm is done
        // The GCD will be in the second to last b
        while result[result.len() - 1].1 != 0 {
            let a = result[result.len() - 2].1 / result[result.len() - 1].1;
            let b = result[result.len() - 2].1 % result[result.len() - 1].1;

            result.push((a, b));
        }

        result
    }

    fn calculate_lcm(mut a: u128, mut b: u128) -> u128 {
        let ab = a * b;

        while b != 0 {
            let remainder = a % b;

            a = b;
            b = remainder;
        }

        ab / a // a*b divided by GCD
    }

    pub fn assign_gcd(
        &self,
        mut layouter: impl Layouter<F>,
        a: u128,
        b: u128,
        coprime: bool, // if true, checks if GCD is 1
    ) -> Result<
        (
            (
                AssignedCell<F, F>, // a
                AssignedCell<F, F>, // b
            ),
            AssignedCell<F, F>, // GCD(a, b)
        ),
        Error,
    > {
        layouter.assign_region(
            || "full euclidian algorithm",
            |mut region| {
                let offset = 0;

                // calculate the Euclidian algorithm steps
                let euclid_steps = Self::euclid_gcd_steps(a, b);

                // enable the selectors
                self.q_range.enable(&mut region, offset)?;

                // assign the first cells
                let cell_a = region.assign_advice(
                    || "a init",
                    self.a,
                    offset,
                    || Value::known(F::from_u128(a)),
                )?;
                let cell_b = region.assign_advice(
                    || "b init",
                    self.b,
                    offset,
                    || Value::known(F::from_u128(b)),
                )?;

                // Store to return in the end
                let mut column_a = vec![cell_a];
                let mut column_b = vec![cell_b];

                // Iterate over the steps and assign the witness accordingly
                for (i, (a, b)) in euclid_steps[1..].iter().enumerate() {
                    // Only enable q_euclid_init on the first step, then only q_euclid_ss
                    if i == 0 {
                        self.q_euclid_init.enable(&mut region, offset + i + 1)?;
                    } else {
                        self.q_euclid_ss.enable(&mut region, offset + i + 1)?;
                    }

                    // Enable the GCD check on that last row, and coprime check if enabled
                    if i == euclid_steps.len() - 2 {
                        self.q_gcd.enable(&mut region, offset + i + 1)?;
                        if coprime {
                            self.q_coprime.enable(&mut region, offset + i + 1)?;
                        }
                    }

                    // Range check is always enabled
                    self.q_range.enable(&mut region, offset + i + 1)?;

                    let cell_a = region.assign_advice(
                        || "a",
                        self.a,
                        offset + i + 1,
                        || Value::known(F::from_u128(a.clone())),
                    )?;

                    let cell_b = region.assign_advice(
                        || "b",
                        self.b,
                        offset + i + 1,
                        || Value::known(F::from_u128(b.clone())),
                    )?;

                    column_a.push(cell_a);
                    column_b.push(cell_b);
                }

                // We return the first two elements (a, b), and the second to last (b) which is GCD(a, b)
                Ok((
                    (
                        column_a.first().unwrap().clone(),
                        column_b.first().unwrap().clone(),
                    ),
                    column_b[column_b.len() - 2].clone(),
                ))
            },
        )
    }

    pub fn assign_lcm(
        &self,
        mut layouter: impl Layouter<F>,
        a: u128,
        b: u128,
    ) -> Result<
        (
            (AssignedCell<F, F>, AssignedCell<F, F>), // a, b
            (AssignedCell<F, F>, AssignedCell<F, F>), // gcd, lcm
        ),
        Error,
    > {
        let ((cell_a, cell_b), cell_gcd) =
            self.assign_gcd(layouter.namespace(|| "Assign GCD for LCM"), a, b, false)?;

        layouter.assign_region(
            || "assign LCM",
            |mut region| {
                let offset = 0;

                let lcm = Self::calculate_lcm(a, b);

                self.q_lcm.enable(&mut region, offset)?;

                let cell_a = cell_a.copy_advice(|| "a", &mut region, self.a, offset)?;
                let cell_b = cell_b.copy_advice(|| "b", &mut region, self.b, offset)?;
                let cell_gcd = cell_gcd.copy_advice(|| "gcd", &mut region, self.a, offset + 1)?;

                let cell_lcm = region.assign_advice(
                    || "lcm",
                    self.b,
                    offset + 1,
                    || Value::known(F::from_u128(lcm)),
                )?;

                Ok(((cell_a, cell_b), (cell_gcd, cell_lcm)))
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.exp, row)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gcd::*;
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::{
            metadata::{Column, Constraint, Gate, Region, VirtualCell},
            FailureLocation, MockProver, VerifyFailure,
        },
        pasta::Fp,
        plonk::Circuit,
    };
    use rand::prelude::SliceRandom;

    fn sample_values_from_vec<T: Clone>(input: &Vec<T>, n: usize) -> Vec<T> {
        let mut rng = rand::thread_rng();
        let mut result = Vec::new();

        if n >= input.len() {
            result = input.clone();
        } else {
            for _ in 0..n {
                let random_item = input.choose(&mut rng).unwrap().clone();
                result.push(random_item);
            }
        }

        result
    }

    mod test_gcd {
        use halo2_proofs::plonk::Any;

        use super::*;

        #[derive(Default, Clone)]
        struct GcdCircuit<const RANGE: usize> {
            a: u128,
            b: u128,
            coprime: bool,
        }

        impl<const RANGE: usize> Circuit<Fp> for GcdCircuit<RANGE> {
            type Config = CoprimeConfig<Fp, RANGE>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                CoprimeConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                // populate the lookup table cells
                config.range_check.load(&mut layouter)?;

                // assign the full Euclid's algorithm
                let (_, cell_gcd) = config.assign_gcd(
                    layouter.namespace(|| "assign gcd block"),
                    self.a,
                    self.b,
                    self.coprime,
                )?;
                // expose the last step which contains the GCD of the two inputs only if self.coprime is not already constraining it to 1
                if !self.coprime {
                    config.expose_public(layouter.namespace(|| "expose the gcd"), cell_gcd, 0)?;
                }

                Ok(())
            }
        }

        #[test]
        fn check_gcd() {
            const RANGE: usize = 2 ^ 64;

            for i in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
                for j in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
                    let res = CoprimeConfig::<Fp, RANGE>::euclid_gcd_steps(i as u128, j as u128);
                    let (_, b_last) = res.last().unwrap();
                    let (_, b_prev) = res[res.len() - 2];
                    let gcd = euclid_u128(i as u128, j as u128);

                    assert_eq!(b_prev, gcd);
                    assert_eq!(b_last, &0);
                }
            }
        }

        #[test]
        fn test_range_check() {
            let k = 9;
            const RANGE: usize = 256;

            // Successful cases
            // Sample 50x50 cases expected to pass
            for i in sample_values_from_vec(&(1..RANGE).collect(), 50) {
                for j in sample_values_from_vec(&(1..RANGE).collect(), 50) {
                    let circuit = GcdCircuit::<RANGE> {
                        a: i as u128,
                        b: j as u128,
                        coprime: false,
                    };

                    let res = CoprimeConfig::<Fp, RANGE>::euclid_gcd_steps(i as u128, j as u128);
                    let (a, b) = res[res.len() - 2];

                    let instance = vec![vec![Fp::from_u128(b.clone())]];
                    let prover = MockProver::<Fp>::run(k, &circuit, instance).unwrap();

                    prover.assert_satisfied();
                }
            }

            // Unsuccessful case
            // Out-of-range `a = b = RANGE`
            let circuit = GcdCircuit::<RANGE> {
                a: RANGE as u128,
                b: RANGE as u128,
                coprime: false,
            };

            let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(RANGE as u64)]]).unwrap();
            assert!(prover.verify().is_err());
        }

        #[test]
        fn test_coprime() {
            let k = 9;
            const RANGE: usize = 256;

            // Successful case
            let circuit = GcdCircuit::<RANGE> {
                a: 4 as u128,
                b: 9 as u128,
                coprime: true,
            };

            let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        fn test_not_coprime() {
            let k = 9;
            const RANGE: usize = 256;

            // Unsuccessful case: GCD(16, 4) = 4, not coprimes
            let circuit = GcdCircuit::<RANGE> {
                a: 16 as u128,
                b: 4 as u128,
                coprime: true,
            };

            let prover = MockProver::run(k, &circuit, vec![vec![]]).unwrap();

            assert!(prover.verify().is_err());
        }
    }

    mod test_lcm {
        use super::*;

        #[derive(Default, Clone)]
        struct LcmCircuit<const RANGE: usize> {
            a: u128,
            b: u128,
        }

        impl<const RANGE: usize> Circuit<Fp> for LcmCircuit<RANGE> {
            type Config = CoprimeConfig<Fp, RANGE>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                CoprimeConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                // populate the lookup table cells
                config.range_check.load(&mut layouter)?;

                // assign the full Euclid's algorithm
                let (_, (_, cell_lcm)) =
                    config.assign_lcm(layouter.namespace(|| "assign lcm block"), self.a, self.b)?;
                // expose the last step which contains the GCD of the two inputs
                config.expose_public(layouter.namespace(|| "expose the lcm"), cell_lcm, 0)?;

                Ok(())
            }
        }

        #[test]
        fn check_lcm() {
            const RANGE: usize = 2 ^ 64;

            for i in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
                for j in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
                    let lcm = CoprimeConfig::<Fp, RANGE>::calculate_lcm(i as u128, j as u128);

                    let gcd = euclid_u128(i as u128, j as u128);
                    let ref_lcm = (i as u128) * (j as u128) / gcd;

                    assert_eq!(ref_lcm, lcm);
                }
            }
        }

        #[test]
        fn test_range_check() {
            let k = 9;
            const RANGE: usize = 256;

            // Successful cases
            // Sample 50x50 cases expected to pass
            for i in sample_values_from_vec(&(1..RANGE).collect(), 50) {
                for j in sample_values_from_vec(&(1..RANGE).collect(), 50) {
                    let circuit = LcmCircuit::<RANGE> {
                        a: i as u128,
                        b: j as u128,
                    };

                    let lcm = CoprimeConfig::<Fp, RANGE>::calculate_lcm(i as u128, j as u128);

                    let instance = vec![vec![Fp::from_u128(lcm)]];
                    let prover = MockProver::<Fp>::run(k, &circuit, instance).unwrap();

                    prover.assert_satisfied();
                }
            }

            // Unsuccessful case
            // Out-of-range `a = b = RANGE`
            let circuit = LcmCircuit::<RANGE> {
                a: RANGE as u128,
                b: RANGE as u128,
            };

            let prover =
                MockProver::run(k, &circuit, vec![vec![Fp::from_u128(RANGE as u128)]]).unwrap();
                
            assert!(prover.verify().is_err());
        }
    }
}
