import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}
variable {n : ℕ}
variable (G : SimpleGraph (Fin n))

/-
# SETUP #
Here we setup the basic probability notion, in conjnction with Graphs, that will be needed for
the proof.
-/

/-
# DEFINING 'EDGES' #
'Edges' is the underlying measure of our random Graph formalization and is foundational.
-/
abbrev Edges := G.edgeSet → Bool -- Determines if edge is in Graph
-- No clue what these do yet
noncomputable instance : Fintype (Edges G) := by exact Fintype.ofFinite (Edges G)
noncomputable instance {u v} :  Decidable (G.Adj u v) := by
    exact Classical.propDecidable (G.Adj u v)
instance : DiscreteMeasurableSpace (Edges G) := by
    exact MeasurableSingletonClass.toDiscreteMeasurableSpace

-- Our measure that maps an edge to its probability of existing
noncomputable
def unif_edge_measure (p : ℝ≥0)(h : p ≤ 1) : Measure Bool := (PMF.bernoulli p h).toMeasure
-- Proof that unif_edge_measure is indeed a probability measure
instance unif_edge_measure_isProbabilityMeasure {p : ℝ≥0}{h: p ≤ 1}:
    IsProbabilityMeasure (unif_edge_measure p h):= by {
        rw [@isProbabilityMeasure_iff]
        simp only [Bool.univ_eq]
        unfold unif_edge_measure
        -- Bruhmetheus Momentum
        simp only [PMF.toMeasure_apply_fintype, Fintype.univ_bool,
          Set.mem_insert_iff, Set.mem_singleton_iff, Bool.eq_false_or_eq_true_self,
          Set.indicator_of_mem, PMF.bernoulli_apply, Finset.mem_singleton, Bool.true_eq_false,
          not_false_eq_true, Finset.sum_insert, cond_true, Finset.sum_singleton, cond_false,
          ENNReal.coe_sub, ENNReal.coe_one]
        simp_all only [ENNReal.coe_le_one_iff, add_tsub_cancel_of_le]
    }
-- Maps an Edgeset to unif_edge_measure
instance unif_edgeset_measure_isProbabilityMeasure (p : ℝ≥0)(h:p ≤ 1) :
    IsProbabilityMeasure (Measure.pi (fun _ : G.edgeSet ↦ unif_edge_measure p h)) :=
    Measure.pi.instIsProbabilityMeasure fun _ ↦ unif_edge_measure p h
-- I think this tell Lean that this is a probability measure i.e. PMF. No clue exactly though
noncomputable
def Prob (p : ℝ≥0)(h: p ≤ 1) : PMF (Edges G) :=
    (Measure.pi (fun _ => unif_edge_measure p h)).toPMF

/-
# Random Graphs Basic #
ATTENTION! Is only correct if ω is correctly formalized!
-/
noncomputable
def R_Graph (ω : Edges G) : SimpleGraph (Fin n) where
    Adj u v := ∃(h : s(u,v) ∈ G.edgeSet), ω ⟨s(u,v),h⟩
    loopless := by simp only [Irreflexive,
        SimpleGraph.mem_edgeSet, SimpleGraph.irrefl,
        IsEmpty.exists_iff, not_false_eq_true, implies_true]
    symm := by
        rintro u v ⟨h1,h2⟩
        observe h : s(v,u) = s(u,v)
        rw [h]; use h1

/-  Show that the probability function works correctly,
    I.E. Edge should exist with probability p! -/
theorem Pr_edge {n : ℕ} (p : ℝ≥0) (h : p ≤ 1)
  (G : SimpleGraph (Fin n)) :
  let P := (Prob G p h).toMeasure;
  ∀(e : Sym2 (Fin n))(h : e ∈ G.edgeSet), P.real {ω | ω ⟨e, h⟩ = true} = p := by
    intro P e H
    unfold Measure.real
    simp [P, Prob, unif_edge_measure,Measure.toPMF_toMeasure]
    sorry

def POW (base : Set α) : Set (Set α) := {A : Set α | A ⊆ base}
/-
# Expected Values (#Cycles smaller than l)#
Will be needed for various proofsteps
-/
/- Define sets of edges -/
abbrev edgesets := POW G.edgeSet → ℕ
noncomputable instance : Fintype (edgesets G) := by
    unfold edgesets
    have finApow : Finite (POW G.edgeSet) → ℕ := by
        unfold POW
    refine Fintype.ofFinite (↑(POW G.edgeSet) → ℕ))
instance : DiscreteMeasurableSpace (edgesets G) := by
    exact MeasurableSingletonClass.toDiscreteMeasurableSpace


/-
# Expected Values (Max Independent Sets) #
Will be needed for various proofsteps
-/
