import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {n : ℕ}
variable (G : SimpleGraph (Fin n))

/-
# SETUP #
Here we setup the basic probability notion, in conjnction with Graphs, that will be needed for
the proof.
-/

abbrev Edges := G.edgeSet → Bool -- Determines if edge is in Graph
-- No clue what these do yet
noncomputable instance : Fintype (Edges G) := by exact Fintype.ofFinite (Edges G)
noncomputable instance : Fintype (G.edgeSet) := by exact Fintype.ofFinite ↑G.edgeSet
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
instance (p : ℝ≥0)(h:p ≤ 1) :
    IsProbabilityMeasure (Measure.pi (fun _ : G.edgeSet ↦ unif_edge_measure p h)) :=
    Measure.pi.instIsProbabilityMeasure fun _ ↦ unif_edge_measure p h
-- I think this tell Lean that this is a probability measure i.e. PMF. No clue exactly though
noncomputable def Prob (p : ℝ≥0){h: p ≤ 1} : PMF (Edges G) :=
    (Measure.pi (fun _ => unif_edge_measure p h)).toPMF
