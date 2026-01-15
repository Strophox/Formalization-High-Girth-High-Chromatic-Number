import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.PseudometrizableLindelof
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.CompletelyRegular

import Formalization.API_Graph

set_option autoImplicit false
set_option linter.style.commandStart false
set_option linter.style.induction false
variable {α : Type*}

namespace API_ℙ

open API_𝔾
open scoped API_𝔾
open MeasureTheory
open scoped ENNReal NNReal
/- =============================================== -/
/- Values -/
structure ℙval where
  val   : ℝ≥0
  proof : val ≤ 1
-- mark as variables
variable (p : ℙval)
variable (n : Nval)
/- =============================================== -/

/- =============================================== -/
/- # DEFS # -/
/- =============================================== -/

/- =============================================== -/
/- Graph Sample Space ⇒
The universe of functions Edges -> Bool -/
abbrev ΩK := (EK n) → Bool
-- Properties :
noncomputable instance : Fintype (ΩK n) := by
  exact Pi.instFintype
instance : DiscreteMeasurableSpace (ΩK n) := by
  exact MeasurableSingletonClass.toDiscreteMeasurableSpace
/- =============================================== -/

/- =============================================== -/
/- Bernoulli Measure ⇒
Cast from a bernoulli PMF -/
noncomputable def μ_bernoulli : Measure Bool :=
  (PMF.bernoulli p.1 p.2).toMeasure
  deriving IsProbabilityMeasure
/- =============================================== -/
/- Defines a Measure over sample space ΩK by taking the product
   of the bernoulli measures over all edges. -/
noncomputable abbrev EKμ : Measure (ΩK n) :=
  Measure.pi fun (_ : EK n) ↦ (μ_bernoulli p)
noncomputable instance EKμIsProbMeas : IsProbabilityMeasure (EKμ p n) := by
  exact Measure.pi.instIsProbabilityMeasure fun _ ↦ μ_bernoulli p
/- =============================================== -/
/- Define a PMF over ΩK -/
noncomputable def EKpmf : PMF (ΩK n) :=
  (EKμ p n).toPMF
/- =============================================== -/

/- =============================================== -/
/- # PROBABILITY # -/
/- =============================================== -/

/- =============================================== -/
noncomputable def F_EsubG (E : PEK n):=
  { (f : ΩK n) | ∀(e : E), f e }
noncomputable def Pr_EsubG (E : PEK n) : ℝ :=
  (EKμ p n).real (F_EsubG n E)
/- =============================================== -/

/- =============================================== -/
noncomputable def F_EdisjG (E : PEK n):=
  { (f : ΩK n) | ∀(e : E), f e = false }
noncomputable def Pr_EdisjG (E : PEK n) : ℝ :=
  (EKμ p n).real (F_EdisjG n E)
/- =============================================== -/

/- =============================================== -/
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
/- =============================================== -/

/- =============================================== -/
/- Subset lemma -/
theorem Pr_subset :
  ∀(F1 F2 : Set (ΩK n)), F1 ⊆ F2 → (EKμ p n).real F1 ≤ (EKμ p n).real F2 := by
  intro F1 F2 fsub
  refine measureReal_mono fsub ?_
  simp only [ne_eq, measure_ne_top, not_false_eq_true]
/- =============================================== -/

/- =============================================== -/
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
/- =============================================== -/

/- =============================================== -/
@[scoped simp 10]
/- Pr[e ∈ E(G)] = p -/
theorem Pre_exists (e : EK n) :
Pr_EsubG p n {e} = p.val := by
  rw [(PrE_subs p n {e})]; simp only [Set.ncard_singleton, pow_one]
/- =============================================== -/

/- =============================================== -/
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
/- =============================================== -/
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
/- =============================================== -/

/- =============================================== -/
/- If Probability > 1 then there exists a graph -/
theorem f_exists (F : Set (ΩK n)) :
  0 < (EKμ p n).real F → ∃f, f ∈ F := by
  intro h
  set M := (EKμ p n)
  simp_all only [Measure.real_def]
  by_contra cnt; push_neg at cnt
  have t : F = ∅ := Set.eq_empty_of_forall_notMem cnt
  subst t
  simp only [measure_empty, ENNReal.toReal_zero, lt_self_iff_false] at h
/- If Probability < 1 then there exists a graph in the complement -/
theorem f_complement_exists (F : Set (ΩK n)) :
  (EKμ p n).real F < 1 → ∃f, f ∈ Fᶜ := by
  intro h
  set M := (EKμ p n)
  simp_all only [Measure.real_def]
  have t0 : Disjoint F Fᶜ := by
    exact Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a_1 ↦ a_1
  have t1 : M (F ∪ Fᶜ) = 1 := by
    have t11 : (F ∪ Fᶜ) = (Set.univ : Set (ΩK n)) := by exact Set.union_compl_self F
    rw [t11]; simp only [measure_univ]
  have t2 : MeasurableSet Fᶜ := by
    exact DiscreteMeasurableSpace.forall_measurableSet Fᶜ
  rw [measure_union t0 t2] at t1
  by_contra cnt; push_neg at cnt
  have t : Fᶜ = ∅ := Set.eq_empty_of_forall_notMem cnt
  rw [t] at t1; simp only [measure_empty, add_zero] at t1
  simp_all only [ENNReal.toReal_one, lt_self_iff_false]
/- =============================================== -/

/- =============================================== -/
/- # CONVERSION # -/
/- =============================================== -/

/- =============================================== -/
/- Convert ΩK to SimpleGraph -/
def ΩKtoFinGraph : ΩK n → Fingraph n :=
  fun f ↦ ({
    Adj u v := u ≠ v ∧ ( (h : u ≠ v) → f ⟨s(u,v),h⟩ = true )
    symm := by
      intro a b
      simp only [ne_eq, and_imp]
      intro neq h; specialize h neq
      constructor
      · grind only
      · intro h'
        have : s(a,b) = s(b,a) := by exact Sym2.eq_swap
        simp only [← this, ←h]
  } : Fingraph n)
/- =============================================== -/
/- Convert SimpleGraph to ΩK -/
noncomputable
instance (G : Fingraph n)(a b : Fin n.1) : Decidable (G.Adj a b) := by
  exact Classical.propDecidable (G.Adj a b)
noncomputable
def FinGraphToΩK : Fingraph n → ΩK n :=
  fun G ↦ ( fun e ↦
    Sym2.lift ⟨fun a b ↦ if G.Adj a b then true else false,
      by
      intro a b;
      simp only [Bool.if_false_right, Bool.and_true, decide_eq_decide]
      exact SimpleGraph.adj_comm G a b
    ⟩  e : ΩK n)
/- =============================================== -/
/- Equivalence
   Usage: .1 is from Function to Graph and .2 is from Graph to Function -/
noncomputable
def ΩK_EQ_FinGraph : ΩK n ≃ Fingraph n := {
  toFun := ΩKtoFinGraph n
  invFun := FinGraphToΩK n
  left_inv := by
    intro f
    unfold FinGraphToΩK ΩKtoFinGraph
    simp only [ne_eq, Bool.if_false_right, Bool.decide_and, decide_not, Bool.and_true]
    ext e
    obtain ⟨⟨a,b⟩,ep⟩ := e
    simp only [Sym2.lift_mk]
    generalize gen : f ⟨Quot.mk (Sym2.Rel (Fin n.val)) (a, b), ep⟩ = b
    fin_cases b
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      decide_eq_true_eq]
      rename_i e; simp only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq,
        Sym2.isDiag_iff_proj_eq] at ep
      constructor
      · assumption
      · intro ep'
        simp only [gen]
    · simp only [Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, not_forall, Bool.not_eq_true]
      intro ne; use ne
  right_inv := by
    intro G
    unfold FinGraphToΩK ΩKtoFinGraph
    simp only [ne_eq, Bool.if_false_right, Bool.and_true, Sym2.lift_mk, decide_eq_true_eq]
    induction' G with Adj symm lp
    simp only [SimpleGraph.mk.injEq]
    ext u v
    constructor
    · intro ⟨ha,hb⟩; apply hb at ha; assumption
    · intro adj; constructor
      · unfold Irreflexive at lp
        by_contra cnt
        rw [cnt] at adj
        specialize lp v
        contradiction
      · intro; trivial
}
/- =============================================== -/

/- =============================================== -/
/- # Induced Subgraphs -/
/- =============================================== -/
/- maps values of the induced subvertex set to the new vertices of the subgraph -/
noncomputable
def PVKtoIdxSub {n : Nval}(sub : PVK n) : sub ↪ Fin (sub.toFinset.card) :=
  ⟨ fun i ↦
      ⟨(sub.toFinset.sort (· ≤ ·)).idxOf i.1, by
        have lt : List.idxOf (i.1) (sub.toFinset.sort fun x1 x2 ↦ x1 ≤ x2) + 1
          ≤ (sub.toFinset.sort (· ≤ ·)).length := by
          refine List.idxOf_lt_length_of_mem ?_
          simp only [Finset.mem_sort, Set.mem_toFinset, Subtype.coe_prop]
        grw [@Nat.lt_iff_add_one_le,lt]
        rw [Finset.length_sort]
      ⟩
  ,by
    intro ⟨i1,i1p⟩ ⟨i2,i2p⟩; simp only [Fin.mk.injEq]
    have h : i1 ∈ (Set.toFinset sub).sort := by
      simpa only [Finset.mem_sort, Set.mem_toFinset]
    have h' : i2 ∈ (Set.toFinset sub).sort := by
      simpa only [Finset.mem_sort, Set.mem_toFinset]
    intro a; simp only [Subtype.mk.injEq]
    rw [←List.idxOf_inj h h']; assumption
  ⟩
/- maps new vertices back to the supergraph's -/
noncomputable
def IdxSubtoPVK {n : Nval}(sub : PVK n) : Fin (sub.toFinset.card) ↪ sub :=
  ⟨ fun i ↦
      ⟨(sub.toFinset.sort (· ≤ ·))[i.1], by
        rw [← Set.mem_toFinset]
        rw [← Finset.mem_sort (· ≤ ·)]
        simp only [List.getElem_mem]
      ⟩
  ,by
    intro ⟨i1,i1p⟩ ⟨i2,i2p⟩; simp only [Subtype.mk.injEq]
    intro heq; simp only [Fin.mk.injEq]
    have : List.Nodup (Set.toFinset sub).sort := by
      exact Finset.sort_nodup (Set.toFinset sub) fun a b ↦ a ≤ b
    simp_rw [List.getElem_eq_getElem?_get] at heq
    refine List.getElem?_inj
      (i := i1) (j := i2) ?_ this ?_
    · simp only [Finset.length_sort, i1p]
    · grind only [= List.nodup_iff_count, = get_getElem?, = List.getElem?_eq_none,
      = List.nodup_iff_pairwise_ne, = getElem?_pos, = getElem?_neg]
  ⟩
/- They are a bijection -/
noncomputable
def Idx_EQ_Sub {n : Nval}(sub : PVK n) : Fin (sub.toFinset.card) ≃ sub := {
  toFun := IdxSubtoPVK sub
  invFun := PVKtoIdxSub sub
  right_inv := by
    intro v
    simp only [IdxSubtoPVK, PVKtoIdxSub, Function.Embedding.coeFn_mk, List.getElem_idxOf,
      Subtype.coe_eta]
  left_inv := by
    intro ⟨v,vp⟩;
    simp only [PVKtoIdxSub, IdxSubtoPVK, Function.Embedding.coeFn_mk, Fin.mk.injEq]
    rw [List.idxOf_getElem]
    exact Finset.sort_nodup (Set.toFinset sub) fun x1 x2 ↦ x1 ≤ x2
}
/- Induced subgraph -/
@[local simp]
private
abbrev sub_gt_zero {n}(sub : PVK n)(_ : sub ≠ ∅) : sub.toFinset.card > 0 := by
  rename_i h;by_contra cnt;
  simp only [gt_iff_lt,not_lt, nonpos_iff_eq_zero] at cnt;rw [Finset.card_eq_zero] at cnt
  simp_all only [ne_eq, Set.toFinset_eq_empty]
private
abbrev sub_le_n {n}(sub : PVK n) : sub.toFinset.card ≤ n.1:= by
  exact card_finset_fin_le (Set.toFinset sub)
noncomputable
def G_induce_on {n}(f : ΩK n)(sub : PVK n)(hs : sub ≠ ∅) :
  ΩK (⟨sub.toFinset.card,sub_gt_zero sub hs⟩) :=
  fun e ↦
    ( Sym2.lift ⟨
      fun (a : Fin (sub.toFinset.card)) (b : Fin (sub.toFinset.card)) ↦
        ( if h:a.1=b.1 then false else if f ⟨s(
          ⟨IdxSubtoPVK sub a,by simp only [Fin.is_lt]⟩
          , ⟨IdxSubtoPVK sub b,by simp only [Fin.is_lt]⟩)
          ,by
          simp only [mem_EK_iff]
          obtain ⟨a,ap⟩ := a; obtain ⟨b,bp⟩ := b; simp_all only
          simp only [IdxSubtoPVK, Function.Embedding.coeFn_mk, Fin.eta, ne_eq]
          by_contra cnt; apply h
          apply List.getElem?_inj
            (xs := ((Set.toFinset sub).sort fun x1 x2 ↦ x1 ≤ x2))
          · simpa only [Finset.length_sort]
          · simp only [Finset.sort_nodup]
          · simp_rw [List.getElem_eq_getElem?_get] at cnt
            grind only [= get_getElem?, = List.getElem?_eq_none, = getElem?_pos, = getElem?_neg]
          ⟩ = true
          then true else false
        )
      , by
      simp only [Bool.if_false_right, Bool.decide_eq_true, Bool.and_true]
      intro a b; split_ifs with cif0 cif1 cif2 <;> try grind
      conv => enter [1,1,1]; rw [Sym2.eq_swap]
    ⟩ e.1 )
-- PROPERTIES
-- Preserves Adjacency
theorem not_adj_iff {n}(f : ΩK n)(sub : PVK n)(hs : sub ≠ ∅) :
  ∀(a b : Fin sub.toFinset.card)(neq : a ≠ b),
    (G_induce_on f sub hs) ⟨s(a,b),by
      simp only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq,
      Sym2.isDiag_iff_proj_eq, neq, not_false_eq_true]⟩ = false
    →
    f ⟨s(⟨ IdxSubtoPVK sub a,by simp only [Fin.is_lt] ⟩,
         ⟨ IdxSubtoPVK sub b,by simp only [Fin.is_lt] ⟩),
        by
        obtain ⟨a,ap⟩ := a; obtain ⟨b,bp⟩ := b
        simp only [ne_eq, Fin.mk.injEq] at neq
        simp only [SimpleGraph.edgeSet_top, IdxSubtoPVK, Function.Embedding.coeFn_mk, Fin.eta,
          Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq]
        by_contra cnt; apply neq
        apply List.getElem?_inj
          (xs := ((Set.toFinset sub).sort fun x1 x2 ↦ x1 ≤ x2))
        · simpa only [Finset.length_sort]
        · simp only [Finset.sort_nodup]
        · simp_rw [List.getElem_eq_getElem?_get] at cnt
          grind only [= get_getElem?, = List.getElem?_eq_none, = getElem?_pos, = getElem?_neg]
      ⟩
     = false := by
     intro ⟨a,ap⟩ ⟨b,bp⟩ neq
     unfold G_induce_on
     simp only [Bool.if_false_right, Bool.decide_eq_true, Bool.and_true, Sym2.lift_mk,
       dite_eq_left_iff]
     intro neq2; simp only [ne_eq, Fin.mk.injEq] at neq
     specialize neq2 neq
     simp only [IdxSubtoPVK, Function.Embedding.coeFn_mk, Fin.eta]
     rw [←neq2]; congr



end API_ℙ
