import Mathlib.Tactic
open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option linter.style.commandStart false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : Ω → ℕ} (hX : Measurable X)

#check MeasurableSet.of_discrete

