import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}
variable {n : ℕ}
abbrev graph (n : ℕ) := SimpleGraph (Fin n)

/-
# Probability Space #
Here we setup the basic probability notion, in conjnction with Graphs, that will be needed for
the proof.
-/

abbrev pr_bound (p : ℝ≥0) := 0 ≤ p ∧ p ≤ 1

def Dist_Bernoulli (b : Bool)(p : ℝ≥0)(_ : pr_bound p) : ℝ≥0 := if b then p else 1 - p

/- Probability Space Definition (General) -/
structure PrSpace (Ω : Set α)[Finite Ω] where
    Sa := Ω
    Ev := Ω.powerset -- overwriteable
    Pr : Ev → ℝ≥0
    -- General conditions
    Sa_c : Sa = Ω           -- ENSURES that sample space is the passed argument
    Ev_c : Ev ⊆ Ω.powerset  -- ENSURES that any Event Space is a subset of the powerset
    /- CONDITIONS FOR THE EVENT SPACE -/
    -- Everything happening is a Event
    base : Ω ∈ Ev
    /-  The complement of an Event is still an Event
        Here adapted to treat the set as universe
        Might be a smarter way to do this... (Somhow treat it as a type) -/
    compl : ∀e ∈ Ev, {x ∈ Sa | x ∉ e} ∈ Ev
    -- TODO (Any countable union of Events is still an Event)
    union : sorry
    /- CONDITIONS FOR THE PROBABILITY MEASURE -/
    -- Probabilities are between 0 and 1
    bound : ∀(e : Ev), 0 ≤ Pr e ∧ Pr e ≤ 1
    -- Pr ∅ = 0
    zero :
        Pr ⟨∅,by
        subst Sa_c;apply compl at base
        have null : {x | x ∈ Sa ∧ x ∉ Sa} = ∅ := by {
            simp only [and_not_self, Set.setOf_false]
        }; rw [←null]; trivial
        ⟩ = 0 -- Real annoying that I had to show this explicitly
    -- TODO (The probability of the union of DISJOINT Events
    --      is the same as the sum of their singular probabilities)
    additive : sorry

/- Probability Space Definition (Graph) -/
def PrSpace_G {n : ℕ}(G : graph n) : PrSpace G.edgeSet where
    Sa_c := by rfl
    Ev_c := by rfl
    Pr := sorry
    base := by simp only [Set.mem_powerset_iff, subset_refl]
    compl := by simp only [Set.mem_powerset_iff, Set.sep_subset, implies_true]
    union := sorry
    bound := sorry
    zero := sorry
    additive := sorry

/- THE PLAN
    Establish useable Probability Measure (1)
    Have function that returns probabilities of edges existing (regardless of other edges) (2)
    Have an edgeset ↔ properties interface. (4)
    Maybe you Lucas? I will do generalized properties of Edgesets...
    Obtain probabilities of Properties over edgesets. (5)
    Combine with expected values (6)
-/
