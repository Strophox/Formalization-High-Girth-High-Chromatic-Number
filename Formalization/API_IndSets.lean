import Formalization.API_Probability

set_option autoImplicit false
set_option linter.style.commandStart false
variable {α : Type*}

namespace API_𝕀
open API_ℙ
open scoped API_ℙ
variable (p : ℙval)
variable (n : Nval)

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
def S2_mapTo_EK {n}(I : (PairSet n)) : I.1 ↪ (EK n) :=
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
instance S2_mapTo_EK_inj {n}(I : PairSet n):
  Function.Injective (S2_mapTo_EK I) := by
  exact Function.Embedding.injective (S2_mapTo_EK I)
/- =============================================== -/

/- =============================================== -/
/- Set of all pairs from an Vertex Subset -/
private noncomputable
abbrev SS2 {n}(I : PVK n) : PairSet n := ⟨I.toFinset.powersetCard 2,by
  intro I' h; simp_all only [Finset.mem_powersetCard,Set.subset_toFinset]⟩
-- Properties
-- finite
private noncomputable
instance {n}(I : PVK n) : Fintype ↑(SS2 I).1 := by
  unfold SS2
  exact (
    { val := Finset.powersetCard 2 (Set.toFinset I), proof := _ } : PairSet n
  ).val.fintypeCoeSort
-- Cardinality (I.E cardinality doesn't change after mapping)
private lemma S2_mapTo_EK_Card {n}(I : PairSet n):
  (I.1.attach.image (S2_mapTo_EK I)).card = I.1.card := by {
    have := Finset.card_image_of_injective I.1.attach
      (f := (S2_mapTo_EK I).1) (S2_mapTo_EK I).2
    simp_all only [S2_mapTo_EK , Finset.card_empty, Nat.rec_zero,
      Finset.card_attach, Function.Embedding.coeFn_mk]
  }
/- =============================================== -/

/- =============================================== -/
/- Complete Edgeset of a given Vertex SubSet -/
def EK_sub (I : PVK n) : PEK n :=
  let I' := SS2 I
  -- The complete edgeset on vertexset I
  I'.1.attach.image (S2_mapTo_EK I')
-- Properties
-- Is Finite
noncomputable
instance (I : PVK n) : Fintype (EK_sub n I) := by
  exact Fintype.ofFinite ↑(EK_sub n I)
-- Cardinality of a complete edgeset on a vertex set is (n choose 2)
@[scoped grind =]
theorem EK_sub_card {n}(I : PVK n) : (EK_sub n I).ncard = Nat.choose I.ncard 2 := by {
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
    have card0 : (SS2 I).1.card = Nat.choose I.toFinset.card 2 := by {
      exact Finset.card_powersetCard 2 (Set.toFinset I)
    }
    rw [←card0]; simp only; rw [@Finset.toFinset_coe]
    refine S2_mapTo_EK_Card (SS2 I)
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
/- # INDSETS # -/
/- =============================================== -/

/- Is independent set in Graph -/
noncomputable
abbrev is_IndSetG {n}(f : ΩK n)(I : PVK n) :=
  let noedge (I : PVK n)(v1 v2 : I)(h : v1 ≠ v2) :=
    f ⟨s(v1,v2),by rw[mem_EK_iff];grind only [cases eager Subtype]⟩ = false;
  ∀(v1 v2 : I), (h : v1 ≠ v2) → noedge I v1 v2 h
/- =============================================== -/
/- All independent sets in a given graph -/
noncomputable
abbrev IndSetsG {n}(f : ΩK n) : Finset (PVK n) :=
  {(I : PVK n) | is_IndSetG f I}
-- Properties
-- finite
noncomputable
instance {n}(f : ΩK n) : Fintype (IndSetsG f) := by
  exact Fintype.ofFinite ↑(IndSetsG f)
-- mem finite
noncomputable
instance {n}(f : ΩK n)(I : IndSetsG f) : Fintype I := by
  exact instFintypeElemFinVal n ↑I
-- There will always exist an Independent set
instance {n}(f : ΩK n) : Inhabited (IndSetsG f) := by
  use { }; unfold IndSetsG is_IndSetG; simp only [ne_eq, Subtype.forall, Subtype.mk.injEq,
    Lean.Elab.WF.paramLet, Finset.mem_filter, Finset.mem_univ, IsEmpty.forall_iff, and_self]
instance {n}(f : ΩK n) : Nonempty (IndSetsG f) := by
  exact instNonemptyOfInhabited
-- The size of the any independent set is always ≤ n
theorem MaxIndSet_card {n}{f : ΩK n}(I : IndSetsG f) : I.1.toFinset.card ≤ n.1 := by
  obtain ⟨I,ip⟩ := I
  have : ∀(I : PVK n), I.toFinset.card ≤ n.1 := by
    intro I'
    exact card_finset_fin_le (Set.toFinset I')
  specialize (this I)
  simp_all only [Set.toFinset_card]
-- A independent set of size n will contain independent sets of any size < n
theorem IndSetG_le {n}(f : ΩK n)(up : SZval n) :
  ∀(I : IndSetsG f), I.1.toFinset.card = up.1 →
  ∀(sz : ℕ)(_ : sz ≤ up.1),∃(I' : IndSetsG f), I'.1.toFinset.card = sz := by
  intro ⟨I,Ip⟩ h sz h'
  by_cases cs : I = ∅
  · subst cs
    simp only [Set.toFinset_empty, Finset.card_empty] at h
    rw [←h] at h'; have : sz = 0 := by linarith
    use ⟨∅,Ip⟩; simp_all only [le_refl, Set.toFinset_empty, Finset.card_empty]
  · rw [←h] at h'
    obtain ⟨I', h_subset, h_card⟩ := Finset.exists_subset_card_eq h'
    use ⟨I',by
      simp only [IndSetsG, is_IndSetG, ne_eq, Subtype.forall, Subtype.mk.injEq, Finset.mem_filter,
        Finset.mem_univ, SetLike.coe_sort_coe, true_and]
      intro a ah b bh hne
      simp only [IndSetsG, is_IndSetG, ne_eq, Subtype.forall, Subtype.mk.injEq, Finset.mem_filter,
        Finset.mem_univ, true_and] at Ip;
      have ah' : a ∈ I := by exact Set.mem_toFinset.mp (h_subset ah)
      have bh' : b ∈ I := by exact Set.mem_toFinset.mp (h_subset bh)
      specialize (Ip a ah' b bh' hne); assumption
    ⟩
    rw [←h_card]; simp only [Finset.toFinset_coe]
/- =============================================== -/

/- =============================================== -/
/- Maximal Indset -/
@[scoped simp]
def isMax_Indset {n}(f : ΩK n)(Imax : IndSetsG f) :=
  ∀(I : (IndSetsG f)),Imax.1.toFinset.card ≥ I.1.toFinset.card
-- PROPERTIES
-- There always exists a maximal independent set in a graph
private
theorem MaxIndSetSpec {n}(f : ΩK n) :
  ∃(Imax : IndSetsG f), isMax_Indset f Imax := by {
    unfold isMax_Indset
    exact Finite.exists_max
      fun (I : (IndSetsG f)) ↦ (Set.toFinset I.1).card
  }
noncomputable
abbrev MaxIndSet {n}(f : ΩK n) := Classical.choose (MaxIndSetSpec f)
abbrev MaxIndSetP {n}(f : ΩK n) := Classical.choose_spec (MaxIndSetSpec f)
/- =============================================== -/

/- =============================================== -/
/- The size of a maximal independent set i.e. α(G) -/
noncomputable
def αG {n}(f : ΩK n) : ℕ := (MaxIndSet f).1.toFinset.card
-- Properties :
-- An independent set of size sz implies that α(G) ≥ sz
theorem αG_ge {n}(f : ΩK n)(sz : ℕ):
  ( ∃(I : IndSetsG f), I.1.toFinset.card = sz ) → αG f ≥ sz := by
  intro ⟨I,ip⟩; rw [←ip]
  unfold αG
  generalize ch : (MaxIndSet f) = Imax
  unfold MaxIndSet at ch
  have spec := MaxIndSetP f
  rw [ch] at spec
  unfold isMax_Indset at spec
  specialize (spec I)
  simp only [Set.toFinset_card, ge_iff_le] at spec
  simpa only [Set.toFinset_card, ge_iff_le]
/- =============================================== -/

/- =============================================== -/
/- The set of all graphs having α(G) ≥ sz -/
abbrev G_αG_ge {n}(sz : SZval n) := { (f : ΩK n) | αG f ≥ sz.1 }
/- The set of all graphs having α(G) < sz -/
abbrev G_αG_lt {n}(sz : SZval n) := { (f : ΩK n) | αG f < sz.1 }
-- PROPERTIES
-- The set of all graphs having α(G) < sz is equal to the complement of α(G) ≥ sz
theorem αG_lt_eq_ge_complement (sz : SZval n) : G_αG_lt sz = (G_αG_ge sz)ᶜ := by
  unfold G_αG_ge G_αG_lt
  ext f; simp only [Set.mem_setOf_eq, ge_iff_le, Set.mem_compl_iff, not_le]
/- =============================================== -/
/- The set of all graphs having at least one independent set of size sz -/
abbrev G_any_ind_ofsz {n}(sz : SZval n) := ⋃(I ∈ (IndSets_ofsz n sz)),(F_EdisjG n (EK_sub n I))
-- PROPERTIES
/- =============================================== -/
/- General Theorems -/
-- If a graph G has at least one independent set of size sz iff α(G) ≥ sz
theorem G_any_ind_ofsz_iff_αG_ge {n}(sz : SZval n)(f : ΩK n) :
  f ∈ G_any_ind_ofsz sz ↔ αG f ≥ sz.1 := by
  constructor
  · intro h; simp only [Set.mem_iUnion, Finset.mem_powersetCard, Set.toFinset_univ,
    Finset.subset_univ, true_and, exists_prop] at h
    obtain ⟨I,h1,h2⟩ := h; unfold F_EdisjG at h2
    simp only [Set.mem_setOf_eq] at h2

    have mem : (I : PVK n) ∈ IndSetsG f := by
      unfold IndSetsG is_IndSetG
      simp only [ne_eq, Subtype.forall, Subtype.mk.injEq, Lean.Elab.WF.paramLet, Finset.mem_filter,
        Finset.mem_univ, SetLike.coe_sort_coe, true_and]
      intro a ah b bh h; simp only [Subtype.forall, SimpleGraph.edgeSet_top, Set.mem_setOf_eq] at h2
      specialize ( h2 s(a,b) (by simpa only [Sym2.isDiag_iff_proj_eq]) ); apply h2
      simp only [EK_sub, Finset.coe_image, Finset.coe_attach, Set.image_univ, Set.mem_range,
        Subtype.exists, Finset.toFinset_coe, Finset.mem_powersetCard]; use {a,b}
      use (by
        constructor
        · grind only [= Finset.mem_insert, = Set.mem_singleton_iff, = Finset.subset_iff,
          usr Finset.card_ne_zero_of_mem, = Finset.insert_eq_of_mem, = Finset.mem_singleton,
          cases Or]
        · exact Finset.card_pair h
      )
      simp only [S2_mapTo_EK, Finset.card_empty, Nat.rec_zero, OfNat.one_ne_ofNat,
        Function.Embedding.coeFn_mk]
      split <;> try grind only [= Finset.card_empty, usr Finset.card_ne_zero_of_mem,
        = Finset.insert_eq_of_mem]
      rename_i a' b' hq
      have hx : a' ∈ ({a, b} : Finset _) := by
        rw [← Finset.mem_toList, hq]; exact List.mem_cons_self
      have hy : b' ∈ ({a, b} : Finset _) := by
        rw [← Finset.mem_toList, hq]; exact List.mem_of_getLast? rfl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      have : [a', b'].Nodup := by rw [←hq]; exact Finset.nodup_toList _
      grind only [← List.not_mem_nil, → List.Pairwise.of_cons, = List.mem_cons,
        ← List.IsChain.singleton, = List.isChain_cons_cons, = List.nodup_iff_count,
        = Set.mem_singleton_iff, = List.nodup_cons, usr Finset.card_ne_zero_of_mem,
        = List.nodup_iff_pairwise_ne, = List.pairwise_pair, = Finset.insert_eq_of_mem,
        = List.pairwise_cons_cons, ← List.IsChain.nil, ← List.pairwise_singleton,
        = Finset.mem_singleton, ← List.Pairwise.nil, usr List.nodup_nil, → List.Pairwise.isChain,
        usr List.eq_or_mem_of_mem_cons, cases Or]

    have H := αG_ge f; apply H; use ⟨I,mem⟩
    simp only [Finset.toFinset_coe, h1]
  · intro h; simp_all only [ge_iff_le, Set.mem_iUnion, Finset.mem_powersetCard, Set.toFinset_univ,
    Finset.subset_univ, true_and, exists_prop]
    unfold αG at h
    generalize ch : (MaxIndSet f) = Imax
    have : Imax.1.toFinset = (Set.toFinset (MaxIndSet f)) := by
      exact Set.toFinset_inj.mpr (congrArg Subtype.val (id (Eq.symm ch)))
    rw [←this] at h; clear this
    unfold MaxIndSet at ch
    have spec := MaxIndSetP f
    rw [ch] at spec; clear ch
    unfold isMax_Indset at spec
    have t := IndSetG_le f ⟨Imax.1.toFinset.card,MaxIndSet_card Imax⟩ Imax
    simp only [Set.toFinset_card, forall_const] at t
    have t0 : sz.val ≤ Fintype.card ↑↑Imax := by
      simp only [Set.toFinset_card] at h; trivial
    specialize (t sz.1 t0); obtain ⟨I',ip⟩ := t
    use I'.1.toFinset; constructor
    · simpa only [Set.toFinset_card]
    · clear h spec t0 ip
      simp only [F_EdisjG, EK_sub, S2_mapTo_EK, Finset.card_empty, Nat.rec_zero,
        Lean.Elab.WF.paramLet, Function.Embedding.coeFn_mk, SetLike.coe_sort_coe, Subtype.forall,
        OfNat.one_ne_ofNat, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
        Set.coe_toFinset, Finset.mem_powersetCard, Set.subset_toFinset, forall_exists_index,
        forall_and_index, SimpleGraph.edgeSet_top, Set.mem_setOf_eq]
      intro pair ph I mem hq
      split <;> try grind
      rename_i a b heq
      obtain ⟨I',ip'⟩ := I'
      simp only [Finset.mem_filter, Finset.mem_univ,
        is_IndSetG, ne_eq, Subtype.forall, true_and] at ip'
      intro mem; simp only [Subtype.mk.injEq] at mem; simp only [← mem] at ph; simp only [←mem]
      simp only [Sym2.isDiag_iff_proj_eq] at ph
      have hx : a ∈ I := by
        rw [← Finset.mem_toList, heq]; exact List.mem_cons_self
      have hy : b ∈ I := by
        rw [← Finset.mem_toList, heq]; exact List.mem_of_getLast? rfl
      have hx' : a ∈ I' := by (expose_names; exact mem_1 hx)
      have hy' : b ∈ I' := by (expose_names; exact mem_1 hy)
      specialize (ip' a hx' b hy' (by simp only [Subtype.mk.injEq, ph, not_false_eq_true]))
      assumption
-- The set of all graphs having at least one independent set of size sz
-- is EQUAL to
-- The set of all graphs having α(G) ≥ sz
theorem G_any_ind_ofsz_eq_G_αG_ge {n}(sz : SZval n) :
  G_any_ind_ofsz sz = G_αG_ge sz := by
  ext f
  constructor
  · intro h; rw [G_any_ind_ofsz_iff_αG_ge] at h
    simp_all only [Set.mem_setOf_eq, ge_iff_le]
  · intro h; rw [G_any_ind_ofsz_iff_αG_ge]
    simp_all only [Set.mem_setOf_eq, ge_iff_le]
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
noncomputable
def PrI {n}(I : PVK n) : ℝ := Pr_EdisjG p n (EK_sub n I)
-- Properties
-- eval = (1-p)^(|I|.choose 2)
@[scoped grind =]
theorem PrI_val {n}(I : PVK n) : (PrI p I) = (1-p.1)^(Nat.choose I.ncard 2) := by {
  unfold PrI; rw [PrE_disj]; congr; grind only [= EK_sub_card]
}
/- =============================================== -/

/- =============================================== -/
/- Probability of a graph having α(G) ≥ sz -/
noncomputable
def PrI_αG_gt (p : ℙval){n}(sz : SZval n) :=
  (EKμ p n).real ( G_αG_ge sz )
/- =============================================== -/
/- Probability of a graph having at least one independent set of size sz -/
noncomputable
def PrI_ofsz (p : ℙval){n}(sz : SZval n) :=
  (EKμ p n).real ( G_any_ind_ofsz sz )
-- unfolded
noncomputable
def PrI_ofsz' (p : ℙval)(n sz : ℕ)(bd : 0 < n)(h : sz ≤ n) :=
  let n : Nval := ⟨n,bd⟩;
  let sz : SZval n := ⟨sz,h⟩;
  PrI_ofsz p sz
-- upper bounded
private noncomputable
def UB_PrI_ofsz (p : ℙval){n}(sz : SZval n) :=
  ∑(I ∈ (IndSets_ofsz n sz)), Pr_EdisjG p n (EK_sub n I)
-- eval = n choose sz * (1 - p)^(sz choose 2).
private lemma UB_PrI_ofsz_eval (p : ℙval){n}(sz : SZval n) :
  UB_PrI_ofsz p sz = (n.1.choose sz.1) * (1 - p.1)^(sz.1.choose 2) := by
  unfold UB_PrI_ofsz
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
   Note that this is equivalent to the Probability that [α(G) ≥ sz].
   [[αG_ge]] gives us the explicit proof of that fact -/
theorem UB_PrI_αG_gt (p : ℙval){n}(sz : SZval n):
  (PrI_αG_gt p sz) ≤ (n.1.choose sz.1) * (1 - p.1)^(sz.1.choose 2) := by
  let IndSZ := (IndSets_ofsz n sz);
  rw [←UB_PrI_ofsz_eval]
  unfold PrI_αG_gt; rw [←G_any_ind_ofsz_eq_G_αG_ge]
  unfold G_any_ind_ofsz UB_PrI_ofsz Pr_EdisjG
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


end Probability


end API_𝕀
