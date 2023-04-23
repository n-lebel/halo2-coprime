use halo2_proofs::circuit::Value;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Instance, Selector},
    poly::Rotation,
    arithmetic::FieldExt
};

mod table;
use table::*;

/// This module assigns the GCD of two integers through Euclid's algorithm, 
/// and assigns the LCM in another region. The results can be then exposed
/// in an instance column.
///
// +-----------+-------+------------+----------+-------+-------+----------+
// | col_a     | col_b | col_c      | q_euclid | q_gcd | q_lcm | q_range  |
// +-----------+-------+------------+----------+-------+-------+----------+
// | a         | b     | a // b     | 0        | 0     | 0     | 1        |
// | b         | a%b   | b // (a%b) | 1        | 0     | 0     | 1        |
// | ...       | ...   | ...        | 1        | 0     | 0     | 1        |
// | gcd(a, b) | 0     | 0          | 1        | 1     | 0     | 1        |
// |           |       |            |          |       |       |          |
// | a         | b     | gcd(a, b)  | 0        | 0     | 1     | 0        |
// | lcm(a, b) |       |            | 0        | 0     | 0     | 0        |
// +-----------+-------+------------+----------+-------+-------+----------+



#[derive(Debug, Clone)]
pub struct CoprimeConfig<F: FieldExt, const RANGE: usize> {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    exp: Column<Instance>,

    range_check: RangeTableConfig<F, RANGE>,

    q_range: Selector,
    q_euclid: Selector,
    q_gcd: Selector,
    q_lcm: Selector,
}


impl<F: FieldExt, const RANGE: usize> CoprimeConfig<F, RANGE> {
    fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        let exp = meta.instance_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(exp);

        let range_check = RangeTableConfig::<F, RANGE>::configure(meta);

        let q_range = meta.complex_selector();
        let q_euclid = meta.selector();
        let q_gcd = meta.selector();
        let q_lcm = meta.selector();

        // Verify that this is a valid Euclid's algorithm step
        // No overflows possible in the constraints as long as RANGE doesn't exceed p/2
        meta.create_gate("euclid's algorithm check", |meta| {
            let q_euclid = meta.query_selector(q_euclid);

            let a_prev = meta.query_advice(a, Rotation::prev());
            let b_prev = meta.query_advice(b, Rotation::prev());
            let div_prev = meta.query_advice(c, Rotation::prev());

            let a_cur = meta.query_advice(a, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur());

            Constraints::with_selector(
                q_euclid,
                [
                    ("a_cur == b_prev", a_cur - b_prev.clone()),
                    (
                        "a_prev == b_prev * div_prev + b_cur",
                        b_prev * div_prev + b_cur - a_prev,
                    ),
                ],
            )
        });

        // Verify that the given row is a final state of a Euclid algorithm
        // Means only the first row is nonzero
        meta.create_gate("gcd check", |meta| {
            let q_gcd = meta.query_selector(q_gcd);

            let a_cur = meta.query_advice(a, Rotation::cur()); // GCD
            let b_cur = meta.query_advice(b, Rotation::cur()); // 0
            let c_cur = meta.query_advice(c, Rotation::cur()); // 0

            Constraints::with_selector(q_gcd, [("b_cur = 0", b_cur), ("c_cur = 0", c_cur)])
        });

        // Verify that the provided LCM = a * b / GCD(a, b)
        // No overflows possible in the constraints as long as RANGE doesn't exceed p/2
        meta.create_gate("lcm check", |meta| {
            let q_lcm = meta.query_selector(q_lcm);

            let a_cur = meta.query_advice(a, Rotation::cur()); // a
            let b_cur = meta.query_advice(b, Rotation::cur()); // b
            let c_cur = meta.query_advice(c, Rotation::cur()); // GCD

            let a_next = meta.query_advice(a, Rotation::next()); // LCM

            Constraints::with_selector(
                q_lcm,
                [("lcm * gcd == a_cur * b_cur", a_cur * b_cur - c_cur * a_next)],
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

        meta.lookup(|meta| {
            let q_range = meta.query_selector(q_range);
            let c_cur = meta.query_advice(c, Rotation::cur());

            vec![(q_range * c_cur, range_check.value)]
        });

        CoprimeConfig {
            a,
            b,
            c,
            exp,
            range_check,
            q_range,
            q_euclid,
            q_gcd,
            q_lcm,
        }
    }

    fn euclid_gcd_steps(mut a: u128, mut b: u128) -> Vec<(u128, u128, u128)> {
        let mut steps_data = Vec::new();

        while b != 0 {
            let quotient = a / b;
            let remainder = a % b;
            steps_data.push((a, b, quotient));

            a = b;
            b = remainder;
        }

        steps_data.push((a, b, 0));

        steps_data
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
                let mut cell_a = region.assign_advice(
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
                region.assign_advice(
                    || "div init",
                    self.c,
                    offset,
                    || Value::known(F::from_u128(a / b)),
                )?;

                // Store to return in the end
                let initial_cell_a = cell_a.clone();
                let initial_cell_b = cell_b.clone();

                // iterate over the steps and assign the witness accordingly
                for (i, (a, b, div)) in euclid_steps[1..].iter().enumerate() {
                    self.q_euclid.enable(&mut region, offset + i + 1)?;
                    self.q_range.enable(&mut region, offset + i + 1)?;

                    // enable the GCD check on that last row
                    if i == euclid_steps.len() - 1 {
                        println!("Success");
                        self.q_gcd.enable(&mut region, offset + i + 1)?;
                    }

                    cell_a = region.assign_advice(
                        || "a",
                        self.a,
                        offset + i + 1,
                        || Value::known(F::from_u128(a.clone())),
                    )?;

                    region.assign_advice(
                        || "b",
                        self.b,
                        offset + i + 1,
                        || Value::known(F::from_u128(b.clone())),
                    )?;

                    region.assign_advice(
                        || "div",
                        self.c,
                        offset + i + 1,
                        || Value::known(F::from_u128(div.clone())),
                    )?;
                }

                Ok(((initial_cell_a, initial_cell_b), cell_a))
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
            (AssignedCell<F, F>, AssignedCell<F, F>),
            AssignedCell<F, F>,
        ),
        Error,
    > {
        let ((cell_a, cell_b), cell_gcd) =
            self.assign_gcd(layouter.namespace(|| "Assign GCD for LCM"), a, b)?;

        layouter.assign_region(
            || "assign LCM",
            |mut region| {
                let offset = 0;

                let lcm = Self::calculate_lcm(a, b);

                self.q_lcm.enable(&mut region, offset)?;

                let cell_a = cell_a.copy_advice(|| "a", &mut region, self.a, offset)?;
                let cell_b = cell_b.copy_advice(|| "b", &mut region, self.b, offset)?;
                cell_gcd.copy_advice(|| "gcd", &mut region, self.c, offset)?;

                let cell_lcm = region.assign_advice(
                    || "lcm",
                    self.a,
                    offset + 1,
                    || Value::known(F::from_u128(lcm)),
                )?;

                Ok(((cell_a, cell_b), cell_lcm))
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
    use halo2_proofs::{dev::{FailureLocation, MockProver, VerifyFailure},     pasta::Fp,
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
        use super::*;

        #[derive(Default, Clone)]
        struct GcdCircuit<const RANGE: usize> {
            a: u128,
            b: u128,
        }

        impl<F: FieldExt, const RANGE: usize> Circuit<F> for GcdCircuit<RANGE> {
            type Config = CoprimeConfig<F, RANGE>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                CoprimeConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                // populate the lookup table cells
                config.range_check.load(&mut layouter)?;

                // assign the full Euclid's algorithm
                let (_, cell_gcd) =
                    config.assign_gcd(layouter.namespace(|| "assign gcd block"), self.a, self.b)?;
                // expose the last step which contains the GCD of the two inputs
                config.expose_public(layouter.namespace(|| "expose the gcd"), cell_gcd, 0)?;

                Ok(())
            }
        }

        #[test]
        fn check_gcd() {
            const RANGE: usize = 2 ^ 64;

            for i in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
                for j in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
                    let res = CoprimeConfig::<Fp, RANGE>::euclid_gcd_steps(i as u128, j as u128);
                    let (a, b, _) = res.last().unwrap();
                    let gcd = euclid_u128(i as u128, j as u128);

                    assert_eq!(a, &gcd);
                    assert_eq!(b, &0);
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
                    };

                    let res = CoprimeConfig::<Fp, RANGE>::euclid_gcd_steps(i as u128, j as u128);
                    let (a, b, c) = res.last().unwrap();

                    let instance = vec![vec![
                        Fp::from_u128(a.clone()),
                        Fp::from_u128(b.clone()),
                        Fp::from_u128(c.clone()),
                    ]];
                    let prover = MockProver::<Fp>::run(k, &circuit, instance).unwrap();

                    prover.assert_satisfied();
                }
            }

            // Unsuccessful case
            // Out-of-range `a = b = RANGE`
            let circuit = GcdCircuit::<RANGE> {
                a: RANGE as u128,
                b: RANGE as u128,
            };

            let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(RANGE as u64)]]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![
                    VerifyFailure::Lookup {
                        lookup_index: 0,
                        location: FailureLocation::InRegion {
                            region: (1, "full euclidian algorithm").into(),
                            offset: 0
                        }
                    },
                    VerifyFailure::Lookup {
                        lookup_index: 0,
                        location: FailureLocation::InRegion {
                            region: (1, "full euclidian algorithm").into(),
                            offset: 1
                        }
                    },
                    VerifyFailure::Lookup {
                        lookup_index: 1,
                        location: FailureLocation::InRegion {
                            region: (1, "full euclidian algorithm").into(),
                            offset: 0
                        }
                    }
                ])
            );
        }
    }

    mod test_lcm {
        use super::*;

        #[derive(Default, Clone)]
        struct LcmCircuit<const RANGE: usize> {
            a: u128,
            b: u128,
        }

        impl<F: FieldExt, const RANGE: usize> Circuit<F> for LcmCircuit<RANGE> {
            type Config = CoprimeConfig<F, RANGE>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                CoprimeConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                // populate the lookup table cells
                config.range_check.load(&mut layouter)?;

                // assign the full Euclid's algorithm
                let (_, cell_lcm) =
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
            assert_eq!(
                prover.verify(),
                Err(vec![
                    VerifyFailure::Lookup {
                        lookup_index: 0,
                        location: FailureLocation::InRegion {
                            region: (1, "full euclidian algorithm").into(),
                            offset: 0
                        }
                    },
                    VerifyFailure::Lookup {
                        lookup_index: 0,
                        location: FailureLocation::InRegion {
                            region: (1, "full euclidian algorithm").into(),
                            offset: 1
                        }
                    },
                    VerifyFailure::Lookup {
                        lookup_index: 1,
                        location: FailureLocation::InRegion {
                            region: (1, "full euclidian algorithm").into(),
                            offset: 0
                        }
                    }
                ])
            );
        }
    }
}
