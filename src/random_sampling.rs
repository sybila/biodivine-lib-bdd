use crate::{Bdd, BddPointer, BddValuation, BddVariable};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};
use rand::Rng;

/// Describes a method that can be used to sample a random valuation from a [`Bdd`]
/// by sampling random Boolean values for given BDD nodes and skipped variables.
pub trait SamplingMethod {
    /// Sample a random Boolean value for the given BDD node.
    ///
    /// The method takes a mutable reference to `self` to allow for something like [`Rng`]
    /// to be stored in the struct.
    fn sample_decision_node(&mut self, node: BddPointer) -> bool;

    /// Sample a random Boolean value for a variable that does not have a decision node. This
    /// method is not used when sampling paths, it is only required to sample valuations.
    ///
    /// The method takes a mutable reference to `self` to allow for something like [`Rng`]
    /// to be stored in the struct.
    fn sample_skipped_node(&mut self, var: BddVariable) -> bool;
}

/// Sampling which always uses probability 1/2, but ignores BDD structure, meaning the
/// final distribution of results depends heavily on the structure of the BDD.
///
/// ```
/// # use biodivine_lib_bdd::BddVariableSet;
/// # use biodivine_lib_bdd::random_sampling::NaiveSampler;
/// # let set = BddVariableSet::new_anonymous(4);
/// # let bdd = set.eval_expression_string("x_0 & x_1 | x_3");
/// let rng = rand::thread_rng();
/// let mut sampling = NaiveSampler::from(rng);
/// let _ = bdd.random_valuation_sample(&mut sampling);
/// ```
#[derive(Debug, Clone)]
pub struct NaiveSampler<R: Rng + Sized>(R);

impl<R: Rng + Sized> From<R> for NaiveSampler<R> {
    fn from(value: R) -> Self {
        NaiveSampler(value)
    }
}

impl<R: Rng + Sized> SamplingMethod for NaiveSampler<R> {
    fn sample_decision_node(&mut self, _node: BddPointer) -> bool {
        self.0.gen_bool(0.5)
    }

    fn sample_skipped_node(&mut self, _var: BddVariable) -> bool {
        self.0.gen_bool(0.5)
    }
}

/// Sampling that uses a pre-computed vector of bias values to ensure that random sampling
/// is performed in a way that produces a **uniform distribution over the valuations** of the BDD.
///
/// **Note that every instance of uniform sampling is built specifically for the given BDD and
/// only works with this BDD.**
///
/// ```
/// # use biodivine_lib_bdd::BddVariableSet;
/// # use biodivine_lib_bdd::random_sampling::{NaiveSampler, UniformValuationSampler};
/// # let set = BddVariableSet::new_anonymous(4);
/// # let bdd = set.eval_expression_string("x_0 & x_1 | x_3");
/// let rng = rand::thread_rng();
/// let mut sampling = bdd.mk_uniform_valuation_sampler(rng);
/// let _ = bdd.random_valuation_sample(&mut sampling);
/// ```
#[derive(Debug, Clone)]
pub struct UniformValuationSampler<R: Rng + Sized> {
    rng: R,
    ratios: Vec<BigRational>,
}

impl<R: Rng + Sized> SamplingMethod for UniformValuationSampler<R> {
    fn sample_decision_node(&mut self, node: BddPointer) -> bool {
        sample_big_rational_probability(&mut self.rng, &self.ratios[node.to_index()])
    }

    fn sample_skipped_node(&mut self, _var: BddVariable) -> bool {
        self.rng.gen_bool(0.5) // Skipped nodes are already uniform.
    }
}

impl<R: Rng + Sized> UniformValuationSampler<R> {
    /// Create a new instance of [`UniformValuationSampler`] using "raw" random number generator
    /// and weights for individual BDD nodes.
    pub fn from_raw_parts(rng: R, ratios: Vec<BigRational>) -> Self {
        UniformValuationSampler { rng, ratios }
    }

    /// Extract the weights for individual BDD nodes from this valuation sampler.
    pub fn into_ratios(self) -> Vec<BigRational> {
        self.ratios
    }
}

impl Bdd {
    /// Build an instance of [`UniformValuationSampler`] specifically for this [`Bdd`].
    pub fn mk_uniform_valuation_sampler<R: Rng + Sized>(
        &self,
        rng: R,
    ) -> UniformValuationSampler<R> {
        let zero = BigInt::zero();
        let one = BigInt::one();
        let two = BigInt::from(2u32);
        let half = BigRational::new(one.clone(), two.clone());

        let mut ratios = vec![half; self.size()];

        let mut valuation_count = vec![None; self.0.len()];
        valuation_count[0] = Some(zero.clone());
        valuation_count[1] = Some(one.clone());

        let mut stack: Vec<BddPointer> = vec![self.root_pointer()];
        while let Some(node) = stack.last() {
            if valuation_count[node.to_index()].is_some() {
                stack.pop();
            } else {
                let low_pointer = self.low_link_of(*node);
                let high_pointer = self.high_link_of(*node);
                let low_var = self.var_of(low_pointer).0;
                let high_var = self.var_of(high_pointer).0;
                let node_var = self.var_of(*node).0;
                let low = low_pointer.to_index();
                let high = high_pointer.to_index();

                if let (Some(cache_low), Some(cache_high)) =
                    (&valuation_count[low], &valuation_count[high])
                {
                    let low_card = cache_low * (one.clone() << (low_var - node_var - 1));
                    let high_card = cache_high * (one.clone() << (high_var - node_var - 1));
                    let total_card = &low_card + &high_card;
                    valuation_count[node.to_index()] = Some(total_card.clone());
                    ratios[node.to_index()] = BigRational::new(high_card.clone(), total_card);
                    stack.pop();
                } else {
                    if valuation_count[low].is_none() {
                        stack.push(low_pointer);
                    }
                    if valuation_count[high].is_none() {
                        stack.push(high_pointer);
                    }
                }
            }
        }

        UniformValuationSampler { rng, ratios }
    }

    /// Sample a random [`BddValuation`] from this BDD using the provided [`SamplingMethod`].
    ///
    /// Typically, this is either [`NaiveSampler`] (faster, but provides no guarantees
    /// on the distribution of the output data) or [`UniformValuationSampler`] (slower,
    /// but provides guaranteed uniform distribution over all values in the BDD).
    ///
    /// Returns `None` if the BDD is not satisfiable.
    pub fn random_valuation_sample<S: SamplingMethod>(
        &self,
        sampling_method: &mut S,
    ) -> Option<BddValuation> {
        if self.is_false() {
            return None;
        }

        let mut valuation = BddValuation::all_false(self.num_vars());
        let mut node = self.root_pointer();
        for i_var in 0..self.num_vars() {
            let var = BddVariable(i_var);
            if self.var_of(node) != var {
                // Just pick random.
                valuation.set_value(var, sampling_method.sample_skipped_node(var));
            } else {
                let child = if self.low_link_of(node).is_zero() {
                    true
                } else if self.high_link_of(node).is_zero() {
                    false
                } else {
                    sampling_method.sample_decision_node(node)
                };

                valuation.set_value(var, child);
                node = if child {
                    self.high_link_of(node)
                } else {
                    self.low_link_of(node)
                }
            }
        }

        Some(valuation)
    }
}

/// Samples a boolean value where the probability of getting `true` is equal to `prob`.
///
/// The input `prob` must be an arbitrary precision rational number between 0 and 1 (inclusive).
///
/// # Arguments
///
/// * `rng` - A mutable reference to a random number generator implementing `rand::Rng`.
/// * `prob` - The `BigRational` representing the probability of returning `true`.
///
/// # Panics
///
/// Panics if `prob` is not between 0 and 1 (inclusive), or if its denominator is zero.
/// (The `BigRational` type itself usually prevents a zero denominator).
fn sample_big_rational_probability<R: Rng + ?Sized>(rng: &mut R, prob: &BigRational) -> bool {
    // If the rational can be successfully represented as a `u32` ratio, we can use primitives.
    if let (Some(numer), Some(denom)) = (prob.numer().to_u32(), prob.denom().to_u32()) {
        return rng.gen_ratio(numer, denom);
    }

    let n = prob.numer(); // Numerator
    let d = prob.denom(); // Denominator

    // A BigRational is usually reduced, so denom should be positive.
    if d.is_zero() {
        panic!("Invariant violation: Denominator cannot be zero.");
    }

    // Check if 0 <= prob <= 1
    if n < &BigInt::zero() || n > d {
        panic!("Probability must be between 0 and 1 inclusive.");
    }

    // Edge cases for probability 0 or 1
    if n.is_zero() {
        return false;
    }
    if n == d {
        // Since 0 <= prob <= 1, if n == d, prob must be 1
        return true;
    }

    // Generate a random BigInt `r_int` in the range [0, d-1]
    // `gen_range(low..high)` generates in `[low, high)`
    // Note: We need to clone `d` because `gen_range` takes `self` by value.
    let r_int = rng.gen_range(BigInt::zero()..d.clone());

    // Check if `r_int` is less than `n`
    r_int < *n
}

#[cfg(test)]
mod tests {
    use crate::random_sampling::NaiveSampler;
    use crate::{BddValuation, BddVariable, BddVariableSet};

    #[test]
    fn test_uniform_sampling() {
        let set = BddVariableSet::new_anonymous(4);

        // The BDD has 2^3 + 1 satisfying valuations, so the likelihood of sampling (0,0,1,1)
        // should approach `0.11111`.
        let bdd = set.eval_expression_string("x_0 | (!x_0 & !x_1 & x_2 & x_3)");

        let mut target = BddValuation::all_false(4);
        target[BddVariable::from_index(2)] = true;
        target[BddVariable::from_index(3)] = true;

        // First, test uniform sampling:

        let rng = rand::thread_rng();
        let mut uniform = bdd.mk_uniform_valuation_sampler(rng);

        let mut found = 0u32;
        for _ in 0..10_000 {
            let valuation = bdd.random_valuation_sample(&mut uniform).unwrap();
            if valuation == target {
                found += 1;
            }
        }

        // In theory, this is fully random and can return anything. In practice, we expect
        // the result to be within 20% of the expected value, which is 1_111.
        assert!(found > 888 && found < 1_333, "{} not in [888, 1333]", found);

        // Now compare it to naive sampling:
        let rng = rand::thread_rng();
        let mut naive = NaiveSampler::from(rng);

        let mut found = 0u32;
        for _ in 0..10_000 {
            let valuation = bdd.random_valuation_sample(&mut naive).unwrap();
            if valuation == target {
                found += 1;
            }
        }

        // In theory, this is fully random and can return anything. In practice, we expect
        // the result to be within 20% of the expected value, which is 5000.
        assert!(
            found > 4000 && found < 6000,
            "{} not in [4000, 6000]",
            found
        );
    }
}
