import Mathlib

set_option autoImplicit false
set_option linter.style.commandStart false

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*}
namespace API_ℙ
/- # DEFS # -/
/- Values -/
structure ℙval where
  val   : ℝ≥0
  proof : val ≤ 1
structure Nval where
  val   : ℕ
  proof : val > 0
-- mark as variables
variable (p : ℙval)
variable (n : Nval)

/- Graph types and Graph constants -/
abbrev Fingraph := SimpleGraph (Fin n.1) -- Our graph type
abbrev KGraph : Fingraph n := SimpleGraph.completeGraph (Fin n.1) -- A complete Graph

/- Vertex Set -/
abbrev VK := Fin n.1
-- Properties :
instance : Fintype (VK n) := by
  exact Fin.fintype n.val
instance : DecidableEq (VK n) := by
  exact instDecidableEqFin n.val
instance VK_nonempty : Nonempty (VK n) := by
  exact Fin.pos_iff_nonempty.mp n.2

/- Vertex Power Set -/
abbrev PVK := Set (Fin n.1)
noncomputable instance : Fintype (PVK n) := by
  exact Fintype.ofFinite ↑(PVK n)
noncomputable instance (I : PVK n) : Fintype I := by
  exact Fintype.ofFinite ↑I
-- Properties :
instance PVK_nonempty : Nonempty (PVK n) := by
  exact instNonemptyOfInhabited

/- Complete EdgeSet -/
abbrev EK := (KGraph n).edgeSet
-- Properties :
noncomputable instance : Fintype (EK n) := by
  exact Fintype.ofFinite ↑(EK n)
noncomputable instance : DecidableEq (EK n) := by
  exact instDecidableEqOfLawfulBEq
-- Helpers
@[scoped simp 10]
theorem mem_EK_iff : ∀(n : Nval),∀(a b), s(a, b) ∈ EK n ↔ a ≠ b := by {
  intros n a b;
  simp only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, ne_eq]
}

/- Complete EdgePowerSet -/
abbrev PEK := Set (EK n)
-- Properties :
noncomputable instance : Fintype (PEK n) := by
  exact Set.fintype
noncomputable instance : DecidableEq (PEK n) := by
  exact Classical.typeDecidableEq (PEK n)

/- Sets of Edgesets -/
abbrev PPEK := Set (PEK n)
-- Properties :
noncomputable instance : Fintype (PPEK n) := by
  exact Set.fintype
noncomputable instance (E': PPEK n): Fintype E' := by
  exact Fintype.ofFinite ↑E'
noncomputable instance PPEK_Countable (E': PPEK n) : Set.Countable E' := by
  exact Set.to_countable E'

/- Graph Sample Space ⇒
The universe of functions Edges -> Bool -/
abbrev ΩK := (EK n) → Bool
-- Properties :
noncomputable instance : Fintype (ΩK n) := by
  exact Pi.instFintype
instance : DiscreteMeasurableSpace (ΩK n) := by
  exact MeasurableSingletonClass.toDiscreteMeasurableSpace

/- Bernoulli Measure ⇒
Cast from a bernoulli PMF -/
noncomputable def μ_bernoulli : Measure Bool :=
  (PMF.bernoulli p.1 p.2).toMeasure
  deriving IsProbabilityMeasure
/- Defines a Measure over sample space ΩK by taking the product
   of the bernoulli measures over all edges. -/
noncomputable abbrev EKμ : Measure (ΩK n) :=
  Measure.pi fun (_ : EK n) ↦ (μ_bernoulli p)
noncomputable instance EKμIsProbMeas : IsProbabilityMeasure (EKμ p n) := by
  exact Measure.pi.instIsProbabilityMeasure fun _ ↦ μ_bernoulli p
/- Define a PMF over ΩK -/
noncomputable def EKpmf : PMF (ΩK n) :=
  (EKμ p n).toPMF

/- # PROBABILITY # -/
noncomputable def F_EsubG (E : PEK n):=
  { (f : ΩK n) | ∀(e : E), f e }
noncomputable def Pr_EsubG (E : PEK n) : ℝ :=
  (EKμ p n).real (F_EsubG n E)

noncomputable def F_EdisjG (E : PEK n):=
  { (f : ΩK n) | ∀(e : E), f e = false }
noncomputable def Pr_EdisjG (E : PEK n) : ℝ :=
  (EKμ p n).real (F_EdisjG n E)

/- Pr[E' ⊆ E(G)] = p^|E'| -/
@[scoped simp 10]
theorem PrE_subs (E : PEK n):
  Pr_EsubG p n E = (p.1 : ℝ)^(E.ncard) := by {
    unfold Pr_EsubG F_EsubG
    rw [Measure.real_def]
    simp only [EKμ, μ_bernoulli]

    let (e : EK n): Decidable (e ∈ E) := by
      exact Classical.propDecidable _
    let f' : (EK n) → Set Bool :=
      fun e ↦ if e ∈ E then {true} else Set.univ

    have heq : { (f : (ΩK n)) | ∀(e : E), f e } = Set.univ.pi f' := by {
      ext f
      constructor
      · intro h
        -- AESOP WIN
        simp_all only [Subtype.forall, SimpleGraph.edgeSet_top,
          Set.mem_setOf_eq, Bool.univ_eq, Set.mem_pi,
          Set.mem_univ, forall_const, not_false_eq_true, f']
        intro a b
        split
        next h_1 => simp_all only [not_false_eq_true, Set.mem_singleton_iff]
        next h_1 =>
          simp_all only [not_false_eq_true, Set.mem_insert_iff, Set.mem_singleton_iff,
            Bool.eq_false_or_eq_true_self]
        -- AESOP WIN
      · intro h
        simp only [Set.mem_setOf_eq]
        intro e
        have t : f ↑e ∈ f' ↑e := by exact h (↑e) trivial
        simp [f'] at t; assumption
    }

    rw [heq, @Measure.pi_pi, @Finset.prod_apply_ite]
    -- SIMP WON
    simp only [PMF.toMeasure_apply_fintype, Fintype.univ_bool, Finset.mem_singleton,
      Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Set.mem_singleton_iff,
      Set.indicator_of_mem, PMF.bernoulli_apply, cond_true, Finset.sum_singleton,
      Bool.false_eq_true, Set.indicator_of_notMem, add_zero, Finset.prod_const, Bool.univ_eq,
      Set.mem_insert_iff, Bool.eq_false_or_eq_true_self, cond_false, ENNReal.coe_sub,
      ENNReal.coe_one, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
    conv =>
      enter [1,1]
      rw [show ({x | x ∈ E} : Finset _).card = (E.toFinset).card from
        by simp only [Set.toFinset_card, Fintype.card_ofFinset]]
    rw [add_tsub_cancel_of_le ?_]
    pick_goal 2;{ simp only [ENNReal.coe_le_one_iff, p.2] }
    have t : ∀(n : ℕ), (ENNReal.toReal 1)^n = 1 := by exact fun n ↦ one_pow n
    rw [t, mul_one]
    norm_cast; congr
    exact Eq.symm (Set.ncard_eq_toFinset_card' E)
  }

@[scoped simp 10]
/- Pr[E' ∩ E(G) = ∅] = (1-p)^|E'| -/
theorem PrE_disj (E : PEK n):
Pr_EdisjG p n E = ((1 - p.1) : ℝ)^(E.ncard) := by {
  unfold Pr_EdisjG F_EdisjG
  rw [Measure.real_def]
  simp only [EKμ, μ_bernoulli]

  let (e : EK n): Decidable (e ∈ E) := by
    exact Classical.propDecidable _
  let f' : (EK n) → Set Bool :=
    fun e ↦ if e ∈ E then {false} else Set.univ

  have heq : { (f : (ΩK n)) | ∀(e : E), f e = false } = Set.univ.pi f' := by {
    ext f
    constructor
    · -- AESOP WON
      intro a
      simp_all only [Subtype.forall, SimpleGraph.edgeSet_top, Set.mem_setOf_eq, Bool.univ_eq,
      Set.mem_pi, Set.mem_univ,forall_const, not_false_eq_true, f']
      intro a_1 b
      split
      next h => simp_all only [not_false_eq_true, Set.mem_singleton_iff]
      next h =>
        simp_all only [not_false_eq_true, Set.mem_insert_iff, Set.mem_singleton_iff,
        Bool.eq_false_or_eq_true_self]
      -- AESOP WON
    · intro h
      simp only [Set.mem_setOf_eq]
      intro e
      have t : f ↑e ∈ f' ↑e := by exact h (↑e) trivial
      simp [f'] at t; assumption
  }
  rw [heq, @Measure.pi_pi, @Finset.prod_apply_ite]
  simp only [PMF.toMeasure_apply_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Set.mem_singleton_iff,
    Set.indicator_of_notMem, Finset.sum_singleton, Set.indicator_of_mem, PMF.bernoulli_apply,
    cond_false, ENNReal.coe_sub, ENNReal.coe_one, zero_add, Finset.prod_const, Bool.univ_eq,
    Set.mem_insert_iff, Bool.eq_false_or_eq_true_self, cond_true, ENNReal.toReal_mul,
    ENNReal.toReal_pow]
  conv =>
    enter [1,1]
    rw [show ({x | x ∈ E} : Finset _).card = (E.toFinset).card from
      by simp only [Set.toFinset_card, Fintype.card_ofFinset]]
  rw [add_tsub_cancel_of_le ?_]
  pick_goal 2;{ simp only [ENNReal.coe_le_one_iff, p.2] }
  have t : ∀(n : ℕ), (ENNReal.toReal 1)^n = 1 := by exact fun n ↦ one_pow n
  rw [t, mul_one]
  norm_cast;congr
  · refine (Real.toNNReal_eq_toNNReal_iff ?_ ?_).mp ?_
    · grw [p.2]
      · norm_num
      · exact ContractingWith.one_sub_K_ne_top
    · grw [p.2]; norm_num
    · norm_num;exact rfl
  exact Eq.symm (Set.ncard_eq_toFinset_card' E)
}

@[scoped simp 10]
/- Pr[e ∈ E(G)] = p -/
theorem Pre_exists (e : EK n) :
Pr_EsubG p n {e} = p.val := by
  rw [(PrE_subs p n {e})]; simp only [Set.ncard_singleton, pow_one]

/- Union bound lemma 1 (Inclusion)-/
theorem PrE_subs_UB (E' : PPEK n) :
  (EKμ p n).real (⋃(E ∈ E'.toFinset),(F_EsubG n E)) ≤ ∑(E ∈ E'.toFinset), Pr_EsubG p n E := by
  unfold Pr_EsubG
  set M := (EKμ p n);

  simp only [Measure.real_def]; rw [← ENNReal.toReal_sum]
  pick_goal 2;{simp only [Set.mem_toFinset, ne_eq, measure_ne_top, not_false_eq_true, implies_true]}
  apply ENNReal.toReal_mono
  {simp only [ne_eq, ENNReal.sum_eq_top, Set.mem_toFinset, measure_ne_top, and_false, exists_const,
    not_false_eq_true]}

  refine MeasureTheory.measure_biUnion_finset_le E'.toFinset (F_EsubG n)

/- Union bound lemma 2 (Exclusion)-/
theorem PrE_disj_UB (E' : PPEK n) :
  (EKμ p n).real (⋃(E ∈ E'.toFinset),(F_EdisjG n E)) ≤ ∑(E ∈ E'.toFinset), Pr_EdisjG p n E := by
  unfold Pr_EdisjG
  set M := (EKμ p n);

  simp only [Measure.real_def]; rw [← ENNReal.toReal_sum]
  pick_goal 2;{simp only [Set.mem_toFinset, ne_eq, measure_ne_top, not_false_eq_true, implies_true]}
  apply ENNReal.toReal_mono
  {simp only [ne_eq, ENNReal.sum_eq_top, Set.mem_toFinset, measure_ne_top, and_false, exists_const,
    not_false_eq_true]}

  refine MeasureTheory.measure_biUnion_finset_le E'.toFinset (F_EdisjG n)

end API_ℙ
