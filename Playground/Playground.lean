--import Mathlib -- The Kitchen sink.
-- import Mathlib.Tactic.Common
import Mathlib.Combinatorics.SimpleGraph.Basic
--import Mathlib.Combinatorics.SimpleGraph.Girth
--import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.MeasureTheory.MeasurableSpace.Defs
-- import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.MeasureSpace

-- import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory

--import Mathlib.MeasureTheory.MeasurableSpace.Basic
--import Mathlib.Data.ENNReal.Basic -- ℝ≥0∞
import Mathlib.Data.NNReal.Basic -- ℝ≥0
import Init.Notation -- For ℝ≥0 ?...
import Mathlib.Util.Notation3
-- import ImportGraph.Meta -- #min_imports
import Mathlib.Tactic.MinImports

--open SimpleGraph
open MeasureTheory
--open MeasureTheory ProbabilityTheory
--open scoped ENNReal

/-
log: leanprover/lean4:v4.25.0-rc2
-/

set_option linter.style.longLine false -- Disable warning on lines exceeding 100 char lim$it.
set_option autoImplicit false -- NOTE: Idk what this actually does.
--set_option tactic.hygienic false -- NOTE: Idk what this actually does. Some linter stuff I guess.
set_option linter.style.lambdaSyntax false -- Allow using "λx ↦ ..." instead of "fun x ↦ ..."


/- # hello, world
Further information / sources:
* —
---------------------------------------------------------------------------------------------------/

example : 1 + 2 = 3 := by rfl

---------------------------------------------------------------------------------------------------/


/- # hello, world
Further information / sources:
* —
---------------------------------------------------------------------------------------------------/

/-
```lean
theorem MeasureTheory.meas_ge_le_lintegral_div
  {G(n,p) : Type u_1}  -- G(n,p) graphs type ?
  [MeasurableSpace G(n,p)]
  {# : Measure G(n,p)}  -- "#" Measure = count/number of elements(=graphs) divided by total elements(=graps) ?
  {X : G(n,p) → ENNReal}
  (hf : AEMeasurable X #)
  {"n/2" : ENNReal}
  (hε : n/2 ≠ 0)
  (hε' : n/2 ≠ ⊤) :
    # {g : G(n,p) | X g ≥ n/2 } ≤ (∫⁻ (g : G(n,p)), f g ∂#) / (n/2)
```

So we specifically see that we need:
* `G(n,p)` to be a `MeasureableSpace`,
* a counting measure(?) `# : Measure G(n,p)`,
* that `AEMeasurable X #`.
-/
--#check ℝ
abbrev Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }

structure /-𝔊-/G (n : ℕ) (p : Prob) where
  graph : SimpleGraph (Fin n)

variable (n : ℕ) (p : Prob)

def nodes {n : ℕ} {p : Prob} (_g : G n p) := n

def edge_prob {n : ℕ} {p : Prob} (_g : G n p) := p

-- def edge_prob_is_prob {n : ℕ} {p : Prob} (g : G n p) := hp

-- theorem nodes_is_eq_card (g : G n p hp) :
--   g.graph : SimpleGraph (Fin (nodes g))

#check G
abbrev SpecificG := G 2 ⟨0.5, by norm_num⟩
#check SpecificG

#check p.2

-- example : (0.5 : ℝ) ≤ 1 := by norm_num

-- example : (0.5 : ENNReal) ≤ 1 := by
--   refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
--   · trivial
--   · trivial
--   · norm_num
--     simp [ENNReal.toReal]
    --apply?
    -- sorry
  -- apply ENNReal.coe_le_coe.2
  -- simp

  -- refine (ENNReal.toNNReal_le_toNNReal ?_ ?_).mp ?_
  -- · exact Ne.symm (not_eq_of_beq_eq_false rfl)
  -- · exact Ne.symm (not_eq_of_beq_eq_false rfl)
  -- · apply?
  --   sorry

-- example : SpecificG where
--   hp := by sorry
--   graph := sorry
-- example g : G 5 0.5 where
--   hp := by sorry
--   graph := sorry

-- #min_imports in MeasurableSpace

instance G.instMeasurableSpace : MeasurableSpace (G n p) := ⊤

noncomputable
def μ {n : ℕ} {p : Prob} : Measure (G n p) :=
  Measure.sum (fun a ↦ a)

theorem /-MeasureTheory.-/meas_ge_le_lintegral_div
  -- {G n p : Type}  -- G(n,p) graphs type ?
  -- [MeasurableSpace (G n p)]
  -- {μ : Measure (G n p)}  -- "#" Measure = count/number of elements(=graphs) divided by total elements(=graps) ?
  {X : G n p → ENNReal}
  (hf : AEMeasurable X μ)
  -- {"n/2" : ENNReal}
  {m : ENNReal}
  (hε : m ≠ 0)
  (hε' : m ≠ ⊤) :
    μ {g : (G n p) | X g ≥ m/2 } ≤ (∫⁻ (g : G n p), X g ∂μ) / (m/2) := by
  apply MeasureTheory.meas_ge_le_lintegral_div
  · assumption
  · refine ENNReal.div_ne_zero.mpr ?_
    constructor
    · assumption
    · trivial
  · refine ENNReal.div_ne_top hε' ?_
    norm_num

---------------------------------------------------------------------------------------------------/

/- # Measure stuff experiment 01
Further information / sources:
* slop provided by Google's slop machine
---------------------------------------------------------------------------------------------------/

-- The type of possible edges {i,j} with i < j
abbrev Edges (n : ℕ) := { e : Fin n × Fin n // e.1 < e.2 }
--abbrev Edges (n : ℕ) : Finset (Fin n × Fin n) := Finset.filter (λ(n,m) ↦ n < m) --{ e : Fin n × Fin n // e.1 < e.2 }

/-
-- Build the product probability space of independent Bernoulli(p) edges
noncomputable def GnpSampleSpace (n : ℕ) (p : NNReal) (h : p ≤ 1) : Measure (Edge n → Bool) :=
  Measure.pi fun _ => PMF.bernoulli (p : NNReal) h -- "Measure.pi" was simply slopped into existence here.
-/

/-
-- The random graph obtained from an ω : Edge n → Bool
def GnpGraph (n : ℕ) : (Edge n → Bool) → SimpleGraph (Fin n)
| ω =>
  {
    adj := fun i j =>
      if h : i < j then ω ⟨(i, j), h⟩
      else if h' : j < i then ω ⟨(j, i), h'⟩
      else False
    symm := by
      intro i j h
      -- graph is symmetric because ω is symmetric by construction
      by_cases hij : i < j
      · have : j < i := lt_of_le_of_ne (le_of_not_gt hij) (by intro; simpa [*] using h)
        simpa [GnpGraph, hij, this] using h
      · ...
    loopless := ...
  }
-/

-- def G (n : ℕ) (p : ENNReal) (hp : p ≤ 1) : "Type of all" SimpleGraph (Fin n) :=
--   -- TODO
--   let graph_from (s : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) :=
--     sorry
--   sorry

  -- Finset.univ.map Finset (Fin n × Fin n).univ
 -- { (graph_from s) : SimpleGraph (Fin n) | s ∈ Set (Fin n × Fin n).univ}

/-theorem MeasureTheory.meas_ge_le_lintegral_div
  {α : Type u_1}
  [MeasurableSpace α]
  {μ : Measure α}
  {f : α → ENNReal}
  (hf : AEMeasurable f μ)
  {ε : ENNReal}
  (hε : ε ≠ 0)
  (hε' : ε ≠ ⊤) :
    μ {x : α | ε ≤ f x} ≤ (∫⁻ (a : α), f a ∂μ) / ε
-/

-- Why do we not get information about the following?...
#min_imports in Measure
#min_imports in MeasureSpace
--#min_imports in MeasurableSpace
#min_imports in ProbabilityMeasure
#min_imports in IsProbabilityMeasure
#min_imports in MeasureTheory
--ProbabilityTheory
---------------------------------------------------------------------------------------------------/


/- # 'Probability theory in Lean 4 using measure theory'
Further information / sources:
* <https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/>
---------------------------------------------------------------------------------------------------

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {P : Measure ℝ} [IsProbabilityMeasure P]

--variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s

-- Random variable.
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X)
---------------------------------------------------------------------------------------------------/


/- # 'WuS script (Martin Schweizer) examples using measure'
Further information / sources:
* (Help from Google's Gemini.)
---------------------------------------------------------------------------------------------------

example : Fin 2 := 0
example : Fin 2 := 1
example : Fin 2 := 3 -- This is the same as 1.

def CoinOutcome' : Type := Fin 2
--example : CoinOutcome' := 0 -- This doesn't work.
example : CoinOutcome' := ⟨0, by trivial⟩ -- This works.

abbrev CoinOutcome : Type := Fin 2 -- Just a syntactic abbreviation(?)...
example : CoinOutcome := 3

-- Sample space (Ω) for two coin flips.
def Ω_flips : Type := CoinOutcome × CoinOutcome

example : Ω_flips := (0,0)

def Event_AtLeastOne1 : Set Ω_flips :=
  {(0,1), (1,0), (1,1)}

open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def

example : ℙ[mindestens einmal 1] = 3/4
-------------------------------------------------------------------------------/


/- # 'Discrete probability stuff without measure'
Further information / sources:
* <https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/basic.20discrete.20probability/with/538351056>
---------------------------------------------------------------------------------------------------

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
abbrev RandomVariable α β := α → β
abbrev Event β := Finset β

--abbrev Pr (X : RandomVariable α β) (S : Event β) := (Finset.univ.filter (X · ∈ S)).dens
abbrev Pr (X : RandomVariable α β) (S : Event β) := (Finset.univ.filter (λa ↦ X a ∈ S)).dens
abbrev X : RandomVariable (Fin 2) (Fin 2) := id

#eval Pr X ∅
#eval Pr X { 0 }
#eval Pr X { 1 }
#eval Pr X { 0, 1 }

abbrev one_minus_X : RandomVariable (Fin 2) (Fin 2) := (1 - ·) ∘ X

#eval Pr one_minus_X { }
#eval Pr one_minus_X { 0 }
#eval Pr one_minus_X { 1 }
#eval Pr one_minus_X { 0, 1 }

example : Pr X = Pr one_minus_X := funext (by decide +kernel)

abbrev X' : RandomVariable (Fin 2) (Fin 2) := id

abbrev X_add_X' : RandomVariable (Fin 2 × Fin 2) (Fin 3) := fun (a, b) => ⟨(X a).1 + (X' b).1, by grind⟩

#eval Pr X_add_X' {0}
#eval Pr X_add_X' {1}
#eval Pr X_add_X' {2}

example : Pr X_add_X' {1} = 1 / 2 := by decide +kernel
---------------------------------------------------------------------------------------------------/
