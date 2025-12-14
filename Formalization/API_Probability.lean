import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}
namespace API_ℙ
/- # Definitions # -/

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
-- Properties :
instance PVK_nonempty : Nonempty (PVK n) := by
  exact instNonemptyOfInhabited

/- Complete EdgeSet -/
abbrev EK := (KGraph n).edgeSet
-- Properties :
noncomputable instance : Fintype (EK n) := by
  exact Fintype.ofFinite ↑(EK n)
-- Helpers
theorem mem_EK_iff : ∀(n : Nval),∀(a b), s(a, b) ∈ EK n ↔ a ≠ b := by {
  intros n a b;
  simp only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, ne_eq]
}

/- Complete EdgePowerSet -/
abbrev PEK := Set (EK n)
-- Properties :
noncomputable instance : Fintype (PEK n) := by
  exact Set.fintype

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
#check EKμ
/- Define a PMF over ΩK -/
noncomputable def EKpmf : PMF (ΩK n) :=
  (EKμ p n).toPMF

/- # THEOREMS # -/
noncomputable def F_EsubG (E : PEK n):=
  { (f : ΩK n) | ∀(e : E), f e }
noncomputable def Pr_EsubG (E : PEK n) : ℝ :=
  (EKμ p n).real (F_EsubG n E)

/- Pr[E' ⊆ E(G)] = p^|E'| -/
theorem PrE (E : PEK n):
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

/- Pr[e ∈ E(G)] = p -/
theorem Pre (e : EK n) :
Pr_EsubG p n {e} = p.val := by
  rw [(PrE p n {e})]; simp only [Set.ncard_singleton, pow_one]

/- PR[E1 ⊆ E(G)] * PR[E1 ⊆ E(G)] = PR[E1 ∪ E2 ⊆ E(G)] IFF E1 E2 disjoint -/
theorem PrE_union_eq (E1 E2 : PEK n) :
  Disjoint E1 E2 → Pr_EsubG p n (E1 ∪ E2) = Pr_EsubG p n E1 * Pr_EsubG p n E2 := by {
    intros pre
    simp only [PrE]

    have heq : (E1 ∪ E2).ncard = E1.ncard + E2.ncard := by {
      rw [Set.ncard_union_eq ?_ ?_ ?_]
      · assumption
      · exact Set.toFinite E1
      · exact Set.toFinite E2
    }

    have arith0 : ∀(a b : ℕ), (p.val : ℝ)^a * p.val^b = p.val^(a+b) := by {
      intros a b
      norm_cast; exact Eq.symm (pow_add p.val a b)
    }

    rw [heq, arith0]
  }

/- -/
end API_ℙ
