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

/- Probability Space Definition (General) -/
structure PrSpace (Ω : Set α) where
    Sa := Ω
    Ev : Set (Set α)
    Pr : Ev → ℝ≥0
    -- General conditions
    Ev_c : Ev ⊆ Sa.powerset  -- ENSURES that any Event Space is a subset of the powerset
    [ Ev_set : SetLike Ev α]
    /- CONDITIONS FOR THE EVENT SPACE -/
    -- Everything happening is a Event
    base : Sa ∈ Ev
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
        apply compl at base
        have null : {x | x ∈ Sa ∧ x ∉ Sa} = ∅ := by {
            simp only [and_not_self, Set.setOf_false]
        }; rw [←null];trivial
        ⟩ = 0 -- Real annoying that I had to show this explicitly
    -- TODO (The probability of the union of DISJOINT Events
    --      is the same as the sum of their singular probabilities)
    additive : sorry

/- Probability Space Definition (Graph) -/
noncomputable
def PrSpace_G {n : ℕ}(G : graph n)(p : ℝ≥0)(bound : p ≤ 1) : PrSpace G.edgeSet where
    Sa := G.edgeSet
    Ev := G.edgeSet.powerset
    Ev_c := by rfl
    Ev_set := by exact SetLike.instSubtypeSet
    -- Check if sound!
    -- Hardcoded the probability of a specific set appearing
    Pr := fun A ↦ if A.val.ncard = 0 then 0
        else p^(A.val.ncard) * (1-p)^({ a ∈ G.edgeSet | a ∉ A.val }.ncard)
    base := by simp only [Set.mem_powerset_iff, subset_refl]
    compl := by simp only [Set.mem_powerset_iff, Set.sep_subset, implies_true]
    union := sorry
    bound := by
        simp only [zero_le, true_and, Subtype.forall, Set.mem_powerset_iff]
        intro A h
        split_ifs with cif
        · simp only [zero_le]
        · generalize SimpleGraph.edgeSet G = B at *
          have leOne : ∀(p : ℝ≥0), ∀x, p ≤ 1 → p^x ≤ 1 := by {
            intros p' n' h'
            induction n'
            · simp only [pow_zero, le_refl]
            · rw [@npow_add]; norm_num
              rename_i n'' IH
              grw[IH, h']; norm_num
          }
          grw [leOne, leOne]
          · simp only [mul_one, le_refl]
          · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
          · assumption
    zero := by simp only [Set.ncard_empty, ↓reduceIte]
    additive := sorry
/- SANITY CHECKS -/
example (p : ℝ≥0)(pr_bound) :
    let W := PrSpace_G (graph n) p (by omega);
    ∀(E1 E2 : W.Ev), E1 ⊆ E2 → W.Pr E1 ≤ W.Pr E2
/- THE PLAN
    Establish useable Probability Measure (1)
    Have function that returns probabilities of edges existing (regardless of other edges) (2)
    Have an edgeset ↔ properties interface. (4)
    Maybe you Lucas? I will do generalized properties of Edgesets...
    Obtain probabilities of Properties over edgesets. (5)
    Combine with expected values (6)
-/
