import Mathlib
import Formalization.API_Probability

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}
open API_ℙ
open scoped API_ℙ
variable (n : Nval)
variable (p : ℙval)

namespace API_𝕀
/- Function that maps a set of size 2 to an edge (Is EMBEDDING) -/
private noncomputable
def S2_mapTo_EK (I : Finset (Finset (Fin n.1)))(pre : ∀i, i ∈ I → i.card = 2) :
I ↪ (EK n) :=
  ⟨fun ⟨S,h_mem⟩ ↦ match h : S.toList with
  -- The mapping
  | a::b::[] => ( ⟨ s(↑a,↑b),by
      have : List.Nodup S.toList := by {exact Finset.nodup_toList S}
      simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
        List.nodup_nil, and_self, and_true, SimpleGraph.edgeSet_top, Set.mem_setOf_eq,
        Sym2.isDiag_iff_proj_eq] ⟩ : (EK n) )
  -- Proof that all other cases cannot happen
  | [] => by
    simp_all only [Finset.toList_eq_nil]
    specialize (pre ∅ h_mem); contradiction
  | [a] => by
    simp_all only [Finset.toList_eq_singleton_iff]
    specialize (pre {a} h_mem)
    simp only [Finset.card_singleton, OfNat.one_ne_ofNat] at pre
  | a::b::c::S' => by
    exfalso; have : (a :: b :: c :: S').length ≥ 3 := by
      grind only [= List.length_cons,= Finset.length_toList, cases eager Subtype]
    grind only [= List.length_cons, = Finset.length_toList, cases eager Subtype],
  by { -- PROOF OF INJECTIVITY
    simp_all only [Function.Injective]
    intro pa pb H
    obtain ⟨pa,pas⟩ := pa; obtain ⟨pb,pbs⟩ := pb
    simp_all only [Finset.card_empty, Nat.rec_zero, Subtype.mk.injEq]
    have t : pa.toList.length = pa.card := by exact Finset.length_toList pa
    split at H <;> expose_names
    · split at H <;> expose_names
      · simp_all only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        ext x
        obtain ⟨h0,h1⟩|⟨h0,h1⟩ := H
        · subst h0 h1; rw [←heq_1] at heq
          rw [← Finset.mem_toList, heq, Finset.mem_toList]
        · subst h0 h1
          have t0 : ∀c, c ∈ pa.toList ↔ c = a ∨ c = b := by grind only [← List.not_mem_nil,
            = List.mem_cons, usr List.eq_or_mem_of_mem_cons, cases Or]
          have t1 : ∀c, c ∈ pb.toList ↔ c = a ∨ c = b := by grind only [← List.not_mem_nil,
            = List.mem_cons, usr List.eq_or_mem_of_mem_cons, cases Or]
          constructor
          · intro hq
            have t0': x ∈ pa.toList := by exact Finset.mem_toList.mpr hq
            rw [t0] at t0'; obtain tt|tt := t0' <;> rw [tt]
            · have t1': a ∈ pb.toList := by
                simp_all only [List.mem_cons, List.not_mem_nil, or_false,
                implies_true, or_true]
              simp only [Finset.mem_toList] at t1'; assumption
            · have t1': b ∈ pb.toList := by
                simp_all only [List.mem_cons, List.not_mem_nil, or_false, implies_true, true_or]
              simp only [Finset.mem_toList] at t1'; assumption
          · intro hq
            have t0': x ∈ pb.toList := by exact Finset.mem_toList.mpr hq
            rw [t1] at t0'; obtain tt|tt := t0' <;> rw [tt]
            · have t1': a ∈ pa.toList := by simp_all only [List.mem_cons, List.not_mem_nil,
              or_false, implies_true, true_or]
              simp only [Finset.mem_toList] at t1'; assumption
            · have t1': b ∈ pa.toList := by simp_all only [List.mem_cons, List.not_mem_nil,
              or_false, implies_true, or_true]
              simp only [Finset.mem_toList] at t1'; assumption
      · grind only [= Finset.card_empty, = List.length_cons, = Finset.length_toList]
      · grind only
      · grind only
    · simp_all only [List.length_nil, OfNat.zero_ne_ofNat]
    · simp_all only [List.length_cons, List.length_nil, zero_add, OfNat.one_ne_ofNat]
    · simp_all only [List.length_cons, Nat.reduceEqDiff]
  }
  ⟩
-- Properties
instance S2_mapTo_EK_inj (I : Finset (Finset (Fin n.1)))(pre : ∀i, i ∈ I → i.card = 2) :
  Function.Injective (S2_mapTo_EK n I pre) := by
  exact Function.Embedding.injective (S2_mapTo_EK n I pre)

/- Set of all pairs(Finset) from a PVK I-/
private noncomputable
abbrev SS2 (I : PVK n) := I.toFinset.powersetCard 2
-- Properties :
private noncomputable -- SS2 is Fintype
instance (I : PVK n) : Fintype (SS2 n I) := by
  exact (SS2 n I).fintypeCoeSort
private -- Cardinality
lemma S2_mapTo_EK_Card (I : Finset (Finset (Fin n.1)))(pre : ∀i, i ∈ I → i.card = 2) :
  (I.attach.image (S2_mapTo_EK n I pre)).card = I.card := by {
    have := Finset.card_image_of_injective I.attach
      (f := (S2_mapTo_EK n I pre).1) (S2_mapTo_EK n I pre).2
    simp_all only
      [S2_mapTo_EK , Finset.card_empty, Nat.rec_zero,
      Finset.card_attach, Function.Embedding.coeFn_mk]
  }

/- Complete Edgeset of a given Vertex set -/
def EK_sub (I : PVK n) : PEK n :=
  -- Prerequesites
  let I' := SS2 n I
  have ht : ∀i, i ∈ I' → i.card = 2 := by
    intro i I2; subst I'
    simp only [Finset.mem_powersetCard, Set.subset_toFinset] at I2
    obtain ⟨I2L,I2R⟩ := I2; assumption;
  -- The complete edgeset on vertexset I
  I'.attach.image (S2_mapTo_EK n I' ht)
-- Properties
noncomputable instance (I : PVK n) : Fintype (EK_sub n I) := by
  exact Fintype.ofFinite ↑(EK_sub n I)
-- Properties. Cardinality of a complete edgeset on a vertex set is (n choose 2)
@[scoped grind =]
theorem EK_sub_card (I : PVK n) :
  (EK_sub n I).ncard = Nat.choose I.ncard 2
:= by {
  suffices h : (EK_sub n I).toFinset.card = Nat.choose I.toFinset.card 2 by {
    calc
      Set.ncard (EK_sub n I)
      _ = (Set.toFinset (EK_sub n I)).card := by exact Set.ncard_eq_toFinset_card' _
      _ = (Set.toFinset I).card.choose 2 := by assumption
      _ = (Set.ncard I).choose 2 := by {
        have t : (Set.toFinset I).card = I.ncard := by exact Eq.symm (Set.ncard_eq_toFinset_card' I)
        rw [t]
      }
    };
    {
    unfold EK_sub;
    have card0 : (SS2 n I).card = Nat.choose I.toFinset.card 2 := by {
      exact Finset.card_powersetCard 2 (Set.toFinset I)
    }
    rw [←card0]; simp only; rw [@Finset.toFinset_coe]
    refine S2_mapTo_EK_Card n (SS2 n I) ?_
    }
  }

/- Probability of a specific Independent set -/
noncomputable def PrI (I : PVK n) : ℝ := Pr_EdisjG p n (EK_sub n I)
/- The value of PrI -/
theorem PrI_val (I : PVK n) : (PrI n p I) = (1-p.1)^(Nat.choose I.ncard 2) := by {
  unfold PrI; rw [PrE_disj]; congr; grind only [= EK_sub_card]
}

end API_𝕀
