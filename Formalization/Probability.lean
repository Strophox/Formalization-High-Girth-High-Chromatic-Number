import Mathlib
open MeasureTheory ProbabilityTheory SimpleGraph
open scoped ENNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : Ω → ℕ} (hX : Measurable X)

/- # General Probability Structure #
This structure is for defining general probability structures.
Use def to create an instance of it.  -/
structure Probability (α : Type*) where
 EventSpace     : MeasurableSpace α
 P              : Measure α
 isProbability  : IsProbabilityMeasure P
/- EXAMPLE: COIN THROW -/
inductive coin where
| head
| tail
def coinOmega1 : MeasurableSpace coin := MeasurableSpace.generateFrom {{coin.head},{coin.tail}}
instance coin_toss : Probability coin := {
    EventSpace := coinOmega1,
    P := sorry,
    isProbability := (by sorry)
}

#check IsProbabilityMeasure
