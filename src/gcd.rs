use halo2_proofs::circuit::Value;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Instance, Selector},
    poly::Rotation,
};

mod table;
use table::*;

#[derive(Debug, Clone)]
struct GcdConfig<const RANGE: usize> {
    a: Column<Advice>,
    b: Column<Advice>,
    div: Column<Advice>,

    exp: Column<Instance>,

    range_check: RangeTableConfig<Fp, RANGE>,

    q_lookup: Selector,
    q_gcd: Selector,
}

impl<const RANGE: usize> GcdConfig<RANGE> {
    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let div = meta.advice_column();

        let exp = meta.instance_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(exp);

        let range_check = RangeTableConfig::<Fp, RANGE>::configure(meta);

        let q_lookup = meta.complex_selector();
        let q_gcd = meta.selector();

        // Verify that this is a valid Euclid's algorithm step
        // No overflows possible in the constraints as long as RANGE doesn't exceed p/2
        meta.create_gate("euclid's algorithm check", |meta| {
            let q_gcd = meta.query_selector(q_gcd);

            let a_prev = meta.query_advice(a, Rotation::prev());
            let b_prev = meta.query_advice(b, Rotation::prev());
            let div_prev = meta.query_advice(div, Rotation::prev());

            let a_cur = meta.query_advice(a, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur());

            Constraints::with_selector(
                q_gcd,
                [
                    ("a_cur == b_prev", a_cur - b_prev.clone()),
                    (
                        "a_prev == b_prev * div_prev + b_cur",
                        b_prev * div_prev + b_cur - a_prev,
                    ),
                ],
            )
        });

        // Constrain all elements of current row to 0..2^RANGE
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let a_cur = meta.query_advice(a, Rotation::cur());

            vec![(q_lookup * a_cur, range_check.value)]
        });

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let b_cur = meta.query_advice(b, Rotation::cur());

            vec![(q_lookup * b_cur, range_check.value)]
        });

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let div_cur = meta.query_advice(div, Rotation::cur());

            vec![(q_lookup * div_cur, range_check.value)]
        });

        GcdConfig {
            a,
            b,
            div,
            exp,
            range_check,
            q_lookup,
            q_gcd,
        }
    }

    fn euclid_gcd_steps(mut a: u64, mut b: u64) -> Vec<(u64, u64, u64)> {
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

    fn assign(
        &self,
        layouter: &mut impl Layouter<Fp>,
        a: u64,
        b: u64,
    ) -> Result<(AssignedCell<Fp, Fp>, AssignedCell<Fp, Fp>), Error> {
        layouter.assign_region(
            || "full euclidian algorithm",
            |mut region| {
                let offset = 0;

                // calculate the Euclidian algorithm steps
                let euclid_steps = Self::euclid_gcd_steps(a, b);

                // enable the selectors
                self.q_lookup.enable(&mut region, offset)?;

                // assign the first cells
                let mut cell_a = region.assign_advice(
                    || "a init",
                    self.a,
                    offset,
                    || Value::known(Fp::from(a)),
                )?;
                let mut cell_b = region.assign_advice(
                    || "b init",
                    self.b,
                    offset,
                    || Value::known(Fp::from(b)),
                )?;
                region.assign_advice(
                    || "div init",
                    self.div,
                    offset,
                    || Value::known(Fp::from(a / b)),
                )?;

                // iterate over the steps and assign the witness accordingly
                for (i, (a, b, div)) in euclid_steps[1..].iter().enumerate() {
                    self.q_gcd.enable(&mut region, offset + i + 1)?;
                    self.q_lookup.enable(&mut region, offset + i + 1)?;

                    cell_a = region.assign_advice(
                        || "a",
                        self.a,
                        offset + i + 1,
                        || Value::known(Fp::from(a.clone())),
                    )?;
                    cell_b = region.assign_advice(
                        || "b",
                        self.b,
                        offset + i + 1,
                        || Value::known(Fp::from(b.clone())),
                    )?;

                    region.assign_advice(
                        || "div",
                        self.div,
                        offset + i + 1,
                        || Value::known(Fp::from(div.clone())),
                    )?;
                }

                Ok((cell_a, cell_b))
            },
        )
    }

    pub fn expose_public(
        &self,
        layouter: &mut impl Layouter<Fp>,
        cell_a: AssignedCell<Fp, Fp>,
        cell_b: AssignedCell<Fp, Fp>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell_a.cell(), self.exp, row)?;
        layouter.constrain_instance(cell_b.cell(), self.exp, row + 1)?;

        Ok(())
    }
}

#[derive(Default, Clone)]
struct GcdCircuit<const RANGE: usize> {
    a: u64,
    b: u64,
}

impl<const RANGE: usize> Circuit<Fp> for GcdCircuit<RANGE> {
    type Config = GcdConfig<RANGE>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        GcdConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        // populate the lookup table cells
        config.range_check.load(&mut layouter)?;

        // assign the full Euclid's algorithm
        let (result_a, result_b) = config.assign(&mut layouter, self.a, self.b)?;
        // expose the last step which contains the GCD of the two inputs
        config.expose_public(&mut layouter, result_a, result_b, 0)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gcd::*;
    use halo2_proofs::dev::{FailureLocation, MockProver, VerifyFailure};
    use rand::{prelude::SliceRandom, *};

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

    fn euclid_gcd_result(mut a: u64, mut b: u64) -> (u64, u64, u64) {
        while b != 0 {
            let remainder = a % b;

            a = b;
            b = remainder;
        }

        (a, b, 0)
    }

    #[test]
    fn check_gcd() {
        const RANGE: usize = 2 ^ 64;

        for i in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
            for j in sample_values_from_vec(&(1..RANGE).collect(), 5000) {
                let res = GcdConfig::<RANGE>::euclid_gcd_steps(i as u64, j as u64);
                let (a, b, _) = res.last().unwrap();
                let gcd = euclid_u64(i as u64, j as u64);

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
                    a: i as u64,
                    b: j as u64,
                };

                let res = GcdConfig::<RANGE>::euclid_gcd_steps(i as u64, j as u64);
                let (a, b, c) = res.last().unwrap();

                let instance = vec![vec![
                    Fp::from(a.clone()),
                    Fp::from(b.clone()),
                    Fp::from(c.clone()),
                ]];
                let prover = MockProver::<Fp>::run(k, &circuit, instance).unwrap();

                prover.assert_satisfied();
            }
        }

        // Unsuccessful case
        // Out-of-range `a = b = RANGE`
        let circuit = GcdCircuit::<RANGE> {
            a: RANGE as u64,
            b: RANGE as u64,
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
