import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : Ω → ℕ} (hX : Measurable X)

structure Probability (α : Type*) where
 EventSpace     : MeasurableSpace α
 P              : Measure α

#check IsProbabilityMeasure

/- # COIN TOSS #
   coin toss using bools for sides.
   true = heads, false = tails
   TODO: find out how to define instance of a Measure.
-/
def coin_toss : Probability Bool := {
    EventSpace := Bool.instMeasurableSpace,
    P := sorry
}
