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

/- # DEFS # -/
/- A finite set of sets of size 2 -/
structure PairSet where
val : Finset (Finset (Fin n.1))
proof : ∀i, i ∈ val → i.card = 2
-- Properties
instance : Fintype (PairSet n) := by
  let T := { X : (Finset (Finset (Fin n.1))) // ∀i, i ∈ X → i.card = 2};
  have : Fintype T := by
    exact Subtype.fintype fun X : (Finset (Finset (Fin n.1))) ↦ ∀ i ∈ X, i.card = 2;
  let bij : T ≃ PairSet n :=  {
    toFun    := fun x => ⟨x.1,x.2⟩
    invFun   := fun x => ⟨x.1,x.2⟩
    left_inv := by intro b; cases b;rfl
    right_inv := by intro b; cases b;rfl
  }
  exact Fintype.ofEquiv T bij

/- Embedding (Injective function) that maps a set of size 2 to an edge -/
private noncomputable
def S2_mapTo_EK (I : (PairSet n)) : I.1 ↪ (EK n) :=
  ⟨--Mapping
    fun ⟨S,h_mem⟩ ↦ match h : S.toList with
    | a::b::[] => --Only viable case
      ( ⟨--value
        s(↑a,↑b)
      ,--proof that it is a Edge i.e. (EK n)
      by
        have : List.Nodup S.toList := by {exact Finset.nodup_toList S};
        rw [mem_EK_iff]
        simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          not_false_eq_true, List.nodup_nil, and_self, and_true, ne_eq]
      ⟩ : (EK n) )
    -- Proof that all other cases are invalid
    | [] => by
      simp_all only [Finset.toList_eq_nil]
      have := I.2; specialize (this ∅ h_mem); contradiction
    | [a] => by
      simp_all only [Finset.toList_eq_singleton_iff]
      have := I.2; specialize (this {a} h_mem)
      simp only [Finset.card_singleton] at this
      contradiction
    | a::b::c::S' => by
      exfalso
      have := I.2;
      have card : (a :: b :: c :: S').length ≥ 3 := by
        grind only [= List.length_cons,= Finset.length_toList, cases eager Subtype];
      grind only [= List.length_cons, = Finset.length_toList, cases eager Subtype]
  ,--Proof of injectivity
  by
    simp_all only [Function.Injective]
    rintro ⟨pa,pas⟩ ⟨pb,pbs⟩ h
    have t : pa.toList.length = pa.card := by exact Finset.length_toList pa;
    split at h
    · split at h
      · expose_names
        simp_all only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Subtype.mk.injEq,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        obtain ⟨h1,h2⟩|⟨h1,h2⟩ := h <;> (ext x;subst h1 h2)
        · simp_all only; rw [←heq_1] at heq
          rw [← Finset.mem_toList, heq, Finset.mem_toList]
        · simp_all only
          have t0 : ∀c, c ∈ pa.toList ↔ c = a ∨ c = b := by grind only [← List.not_mem_nil,
            = List.mem_cons, usr List.eq_or_mem_of_mem_cons, cases Or]
          have t1 : ∀c, c ∈ pb.toList ↔ c = a ∨ c = b := by grind only [← List.not_mem_nil,
            = List.mem_cons, usr List.eq_or_mem_of_mem_cons, cases Or]
          constructor <;> (intros h'; rw [←Finset.mem_toList])
          · specialize (t0 x); rw [←Finset.mem_toList, t0] at h'
            cases h' <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]
          · specialize (t1 x); rw [←Finset.mem_toList, t1] at h'
            cases h' <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false, implies_true,
              or_true, true_or]
      · grind only [= Finset.card_empty, = List.length_cons, = Finset.length_toList]
      · grind only
      · grind only
    · grind only [= Finset.card_empty, = List.length_nil, = Finset.length_toList]
    · grind only
    · grind only
  ⟩
-- Properties
instance S2_mapTo_EK_inj (I : PairSet n):
  Function.Injective (S2_mapTo_EK n I) := by
  exact Function.Embedding.injective (S2_mapTo_EK n I)

/- Set of all pairs from a PVK I-/
private noncomputable
abbrev SS2 (I : PVK n) : PairSet n := ⟨I.toFinset.powersetCard 2,by
  intro I' h; simp_all only [Finset.mem_powersetCard,Set.subset_toFinset]⟩
-- Properties :
private noncomputable -- SS2 is Fintype
instance (I : PVK n) : Fintype ↑(SS2 n I).1 := by
  unfold SS2
  exact (
    { val := Finset.powersetCard 2 (Set.toFinset I), proof := _ } : PairSet n
  ).val.fintypeCoeSort
-- Cardinality (I.E cardinality doesn't change after mapping)
lemma S2_mapTo_EK_Card (I : PairSet n):
  (I.1.attach.image (S2_mapTo_EK n I)).card = I.1.card := by {
    have := Finset.card_image_of_injective I.1.attach
      (f := (S2_mapTo_EK n I).1) (S2_mapTo_EK n I).2
    simp_all only [S2_mapTo_EK , Finset.card_empty, Nat.rec_zero,
      Finset.card_attach, Function.Embedding.coeFn_mk]
  }

/- Complete Edgeset of a given Vertex set -/
def EK_sub (I : PVK n) : PEK n :=
  -- Prerequesites
  let I' := SS2 n I
  -- The complete edgeset on vertexset I
  I'.1.attach.image (S2_mapTo_EK n I')
-- Properties
noncomputable instance (I : PVK n) : Fintype (EK_sub n I) := by
  exact Fintype.ofFinite ↑(EK_sub n I)
-- Properties. Cardinality of a complete edgeset on a vertex set is (n choose 2)
@[scoped grind =]
theorem EK_sub_card (I : PVK n) : (EK_sub n I).ncard = Nat.choose I.ncard 2
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
    have card0 : (SS2 n I).1.card = Nat.choose I.toFinset.card 2 := by {
      exact Finset.card_powersetCard 2 (Set.toFinset I)
    }
    rw [←card0]; simp only; rw [@Finset.toFinset_coe]
    refine S2_mapTo_EK_Card n (SS2 n I)
    }
  }

/- # PROBABILITY #-/
/- Probability of a specific Independent set appearing in a Graph -/
noncomputable def PrI (I : PVK n) : ℝ := Pr_EdisjG p n (EK_sub n I)
/- The value of PrI -/
theorem PrI_val (I : PVK n) : (PrI n p I) = (1-p.1)^(Nat.choose I.ncard 2) := by {
  unfold PrI; rw [PrE_disj]; congr; grind only [= EK_sub_card]
}

/- Maybe prove that some things about maximal independent set size? -/

/- More definitions for IndSets. -/
private noncomputable
def IndSets_sz (sz : ℕ)(_ : sz ≤ n.1) := (Set.univ : Set (VK n)).toFinset.powersetCard sz
private noncomputable
def PrI_ofsz (sz : ℕ)(h : sz ≤ n.1) :=
  (EKμ p n).real (⋃(I ∈ (IndSets_sz n sz h)),(F_EdisjG n (EK_sub n I)))
private noncomputable
def bounded_PrI_ofsz (sz : ℕ)(h : sz ≤ n.1) :=
  ∑(I ∈ (IndSets_sz n sz h)), Pr_EdisjG p n (EK_sub n I)

/- The Final Proofs for IndSets-/
lemma part2 (sz : ℕ)(h : sz ≤ n.1) :
  bounded_PrI_ofsz n p sz h = (n.1.choose sz) * (1 - p.1)^(sz.choose 2) := by
  sorry
theorem PART2 (sz : ℕ)(h : sz ≤ n.1) :
  (PrI_ofsz n p sz h) ≤ (n.1.choose sz) * (1 - p.1)^(sz.choose 2) := by
  sorry

end API_𝕀
