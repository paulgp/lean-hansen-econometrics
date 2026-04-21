import Mathlib.Probability.Distributions.Gamma

open MeasureTheory ProbabilityTheory

namespace HansenEconometrics

/-- The chi-squared distribution with `k` degrees of freedom, defined as
`Gamma(shape = k/2, rate = 1/2)`. -/
noncomputable def chiSquared (k : ℕ) : Measure ℝ :=
  gammaMeasure ((k : ℝ) / 2) (1 / 2 : ℝ)

@[simp] lemma chiSquared_eq (k : ℕ) :
    chiSquared k = gammaMeasure ((k : ℝ) / 2) (1 / 2 : ℝ) := rfl

lemma isProbabilityMeasure_chiSquared {k : ℕ} (hk : 0 < k) :
    IsProbabilityMeasure (chiSquared k) := by
  refine isProbabilityMeasure_gammaMeasure ?_ ?_
  · exact div_pos (Nat.cast_pos.mpr hk) (by norm_num)
  · norm_num

instance {k : ℕ} [Fact (0 < k)] : IsProbabilityMeasure (chiSquared k) :=
  isProbabilityMeasure_chiSquared (k := k) (Fact.out)

lemma chiSquared_gammaPDF_of_neg {k : ℕ} {x : ℝ} (hx : x < 0) :
    gammaPDF ((k : ℝ) / 2) (1 / 2 : ℝ) x = 0 :=
  gammaPDF_of_neg hx

end HansenEconometrics
