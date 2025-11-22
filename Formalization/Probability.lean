import Mathlib.Tactic
open MeasureTheory ProbabilityTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/- # General Probability Structure #
This structure is for defining general probability structures.
Use def to create an instance of it.  -/
structure Probability (α : Type*) where
 EventSpace     : MeasurableSpace α
 P              : PMF α
/- EXAMPLE: COIN THROW -/
inductive coin where
| head
| tail
def coinOmega1 : MeasurableSpace coin := MeasurableSpace.generateFrom {{coin.head},{coin.tail}}
instance coin_toss : Probability coin := {
    EventSpace := coinOmega1,
    P := sorry
}

#check IsProbabilityMeasure
