import Mathlib.Tactic

set_option autoImplicit false
-- set_option tactic.hygienic false


-- hello, world.
example : 1 + 1 = 2 := by rfl

def fac n := if n = 0 then 0 else n * fac (n-1)

-- This symbol 𝕲/𝔊 (\mathfrak{G}) was used by Paul Erdős
-- and we will too because it looks messed up.
-- (Honourable mentions: 𝕰/𝔈 (E), 𝕾/𝔖 (S), 𝖂/𝔚 (W), 𝖄/𝔜 (Y))
example : ∀(𝕲 : ℕ), 𝕲 = 𝕲 := by intro; rfl


-- Probability theory shenanigans.
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {P : Measure ℝ} [IsProbabilityMeasure P]

--variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s

-- Random variable.
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X)
