import Formalization.API_Probability

set_option autoImplicit false
set_option linter.style.commandStart false
variable {α : Type*}

namespace API_𝕀
open API_ℙ
open scoped API_ℙ
variable (n : Nval)
variable (p : ℙval)

/- =============================================== -/
/- # DEFS # -/
/- =============================================== -/

/- =============================================== -/
/- A finite set of sets with cardinality 2 -/
structure PairSet where
val : Finset (Finset (Fin n.1))
proof : ∀i, i ∈ val → i.card = 2
-- PROPERTIES
-- finite
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
/- =============================================== -/
/- =============================================== -/
/- Embedding (Injective function) that maps a PairSet to an edge -/
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
-- Is injective
@[scoped grind! .]
instance S2_mapTo_EK_inj (I : PairSet n):
  Function.Injective (S2_mapTo_EK n I) := by
  exact Function.Embedding.injective (S2_mapTo_EK n I)
/- =============================================== -/

/- =============================================== -/
/- Set of all pairs from an Vertex Subset -/
private noncomputable
abbrev SS2 (I : PVK n) : PairSet n := ⟨I.toFinset.powersetCard 2,by
  intro I' h; simp_all only [Finset.mem_powersetCard,Set.subset_toFinset]⟩
-- Properties
-- finite
private noncomputable
instance (I : PVK n) : Fintype ↑(SS2 n I).1 := by
  unfold SS2
  exact (
    { val := Finset.powersetCard 2 (Set.toFinset I), proof := _ } : PairSet n
  ).val.fintypeCoeSort
-- Cardinality (I.E cardinality doesn't change after mapping)
private lemma S2_mapTo_EK_Card (I : PairSet n):
  (I.1.attach.image (S2_mapTo_EK n I)).card = I.1.card := by {
    have := Finset.card_image_of_injective I.1.attach
      (f := (S2_mapTo_EK n I).1) (S2_mapTo_EK n I).2
    simp_all only [S2_mapTo_EK , Finset.card_empty, Nat.rec_zero,
      Finset.card_attach, Function.Embedding.coeFn_mk]
  }
/- =============================================== -/

/- =============================================== -/
/- Complete Edgeset of a given Vertex SubSet -/
def EK_sub (I : PVK n) : PEK n :=
  let I' := SS2 n I
  -- The complete edgeset on vertexset I
  I'.1.attach.image (S2_mapTo_EK n I')
-- Properties
-- Is Finite
noncomputable
instance (I : PVK n) : Fintype (EK_sub n I) := by
  exact Fintype.ofFinite ↑(EK_sub n I)
-- Cardinality of a complete edgeset on a vertex set is (n choose 2)
@[scoped grind =]
theorem EK_sub_card (I : PVK n) : (EK_sub n I).ncard = Nat.choose I.ncard 2 := by {
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
/- =============================================== -/

section IndSets
/- =============================================== -/
/- # INDSETS # -/
/- =============================================== -/

/- =============================================== -/
/- A bounded size value -/
structure SZval where
  val : ℕ
  proof : val ≤ n.1
variable (sz : SZval n)
/- =============================================== -/

/- =============================================== -/
/- The set of all possible vertexsets of size sz -/
noncomputable
abbrev IndSets_ofsz := (Set.univ : Set (VK n)).toFinset.powersetCard sz.1
-- Properties
-- finite
noncomputable
instance : Fintype (IndSets_ofsz n sz) := by
  exact (IndSets_ofsz n sz).fintypeCoeSort
-- card = n choose sz
theorem IndSets_ofsz_card :
  (IndSets_ofsz n sz).card = n.1.choose sz.1 := by
  unfold IndSets_ofsz
  simp only [Set.toFinset_univ, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
-- mem card = sz
theorem IndSets_ofsz_mem_card :
  ∀(I : (IndSets_ofsz n sz)), I.1.card = sz.1 := by
  {
    intros I;unfold IndSets_ofsz at I; obtain ⟨I,ip⟩ := I; simp only
    grind only [= Finset.mem_powersetCard]
  }
/- =============================================== -/

/- =============================================== -/
/- All independent sets in a given graph -/
def IndSetsG (f : ΩK n) :=
  let noedge (I : PVK n)(v1 v2 : I)(h : v1 ≠ v2) :=
    f ⟨s(v1,v2),by rw[mem_EK_iff];grind only [cases eager Subtype]⟩ = false;
  let isInd (I : PVK n):= ∀(v1 v2 : I), (h : v1 ≠ v2) → noedge I v1 v2 h
  {(I : PVK n) | isInd I}
-- Properties
-- finite
noncomputable
instance (f : ΩK n) : Fintype (IndSetsG n f) := by
  exact Fintype.ofFinite ↑(IndSetsG n f)
-- mem finite
noncomputable
instance (f : ΩK n)(I : IndSetsG n f) : Fintype I := by
  exact instFintypeElemFinVal n ↑I
-- There will always exist an Independent set
instance (f : ΩK n) : Inhabited (IndSetsG n f) := by
  use { }; unfold IndSetsG; simp only [ne_eq, Subtype.forall, Subtype.mk.injEq, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
instance (f : ΩK n) : Nonempty (IndSetsG n f) := by
  exact instNonemptyOfInhabited
/- =============================================== -/

/- =============================================== -/
/- # MAXIMAL INDSETS # -/
/- =============================================== -/
/- There always exists a maximal independent set in a graph -/
private def MaxIndSetSpec (f : ΩK n) :
  ∃(Imax : PVK n),
  ∀(I : (IndSetsG n f)),Imax.toFinset.card ≥ I.1.toFinset.card := by {
    by_contra cnt
    simp only [not_exists,not_forall] at cnt
    specialize (cnt (Set.univ : PVK n))
    obtain ⟨I,cnt⟩ := cnt
    apply cnt; gcongr; exact fun ⦃a⦄ a_1 ↦ trivial
    -- No clue how I managed this one
  }
-- Obtain such maximal independent set using Axiom of Choice
def MaxIndSet (f : ΩK n) : PVK n := Classical.choose (MaxIndSetSpec n f)
def MaxIndSetP (f : ΩK n) := Classical.choose_spec (MaxIndSetSpec n f)
-- Properties:
-- [TODO]
/- =============================================== -/

/- =============================================== -/
/- The size of a maximal independent set i.e. α(G) -/
noncomputable
def αG (f : ΩK n) : ℕ := (MaxIndSet n f).ncard
-- Properties:
-- [TODO]
/- =============================================== -/

end IndSets

section Probability
open MeasureTheory
open scoped ENNReal NNReal
/- =============================================== -/
/- # PROBABILITY #-/
/- =============================================== -/

/- =============================================== -/
/- Probability of an Independent set I appearing in a Graph -/
noncomputable def PrI (I : PVK n) : ℝ := Pr_EdisjG p n (EK_sub n I)
-- Properties
-- eval = (1-p)^(|I|.choose 2)
@[scoped grind =]
theorem PrI_val (I : PVK n) : (PrI n p I) = (1-p.1)^(Nat.choose I.ncard 2) := by {
  unfold PrI; rw [PrE_disj]; congr; grind only [= EK_sub_card]
}
/- =============================================== -/

/- =============================================== -/
/- The final theorem -/
/- =============================================== -/
-- DEF: Exact probability
noncomputable
def PrI_ofsz (p : ℙval){n}(sz : SZval n) :=
  (EKμ p n).real (⋃(I ∈ (IndSets_ofsz n sz)),(F_EdisjG n (EK_sub n I)))
noncomputable
/- EXACT PROBABILITY not requiring special structures -/
def PrI_ofsz' (p : ℙval)(n sz : ℕ)(bd : 0 < n)(h : sz ≤ n) :=
  let n : Nval := ⟨n,bd⟩;
  let sz : SZval n := ⟨sz,h⟩
  PrI_ofsz p sz
-- DEF: Bounded probability
private noncomputable
def bounded_PrI_ofsz (p : ℙval){n}(sz : SZval n) :=
  ∑(I ∈ (IndSets_ofsz n sz)), Pr_EdisjG p n (EK_sub n I)
/- Eval of Bounded Probability i.e. n choose sz * (1 - p)^(sz choose 2)
   A helper lemma for the final step of the start of part 2. -/
private lemma bounded_PrI_ofsz_val (p : ℙval){n}(sz : SZval n) :
  bounded_PrI_ofsz p sz = (n.1.choose sz.1) * (1 - p.1)^(sz.1.choose 2) := by
  unfold bounded_PrI_ofsz
  simp [EK_sub_card]
  trans ∑ x ∈ IndSets_ofsz n sz, (1 - ↑p.val) ^ sz.val.choose 2
  · apply Finset.sum_congr rfl
    intros x hx
    have t : x.card = sz.1 := by exact IndSets_ofsz_mem_card n sz ⟨x,hx⟩
    rw [t]
  · rw [Finset.sum_const]
    simp only [nsmul_eq_mul] -- Fixes ℕ * ℝ typing issues
    rw [IndSets_ofsz_card]
/- The probability of a graph containing at least one independent set of size sz is
   upper bounded by !!! (n choose sz) * (1 - p)^(sz choose 2) !!!
   Note that this is equivalent to the Probability that [α(G) ≥ sz]. -/
theorem PrI_ofsz_UBval (p : ℙval){n}(sz : SZval n):
  (PrI_ofsz p sz) ≤ (n.1.choose sz.1) * (1 - p.1)^(sz.1.choose 2) := by
  let IndSZ := (IndSets_ofsz n sz);
  rw [←bounded_PrI_ofsz_val]
  unfold bounded_PrI_ofsz PrI_ofsz Pr_EdisjG
  set M := (EKμ p n);

  -- TYPES :(
  simp only [Measure.real_def];rw [← ENNReal.toReal_sum]
  pick_goal 2;{simp only [ne_eq, measure_ne_top, not_false_eq_true, implies_true]}
  apply ENNReal.toReal_mono
  {simp only [ne_eq, ENNReal.sum_eq_top, Finset.mem_powersetCard, Set.toFinset_univ,
    Finset.subset_univ, true_and, measure_ne_top, and_false, exists_const, not_false_eq_true]}
  -- TYPES :(

  refine MeasureTheory.measure_biUnion_finset_le --Union Bound
    (IndSets_ofsz n sz)
    (fun I ↦ F_EdisjG n (EK_sub n I))
/- =============================================== -/
/- This is the first step of part 2 YIPPIE!! -/
end Probability


end API_𝕀
