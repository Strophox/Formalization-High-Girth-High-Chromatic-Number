import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/- # General Probability Structure #
This structure is for defining general probability structures
over a n-size event space -/
structure Probability (α : Type*) where
 EventSpace     : MeasurableSpace α
 Measure        : PMF α

/-==============================================================-/
/-EXAMPLE COIN-/
noncomputable
def coin : Probability Bool where
 EventSpace := MeasurableSpace.generateFrom {{true},{false}}
 Measure := PMF.bernoulli (1/2 : ℝ≥0) (by norm_num)
/-FIRST PROOF YIPPIE!!!!!-/
example:
    coin.Measure false + coin.Measure true = 1 := by
    unfold coin; simp; rw[ENNReal.inv_two_add_inv_two]
/-==============================================================-/

#check IsProbabilityMeasure
