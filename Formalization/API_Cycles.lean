import Mathlib
import Formalization.API_Probability

set_option autoImplicit false
set_option linter.style.commandStart false
set_option linter.style.induction false
variable {α : Type*}

namespace API_ℂ
open API_ℙ
open scoped API_ℙ
variable (n : Nval)
variable (p : ℙval)

/- Length of a cycle must be ≥ 3 -/
structure Cval where
  val : ℕ
  proof : 3 ≤ val
variable (l : Cval)

section Defs
open Equiv
/- =============================================== -/
/- # Defs # -/
/- =============================================== -/

/- =============================================== -/
/- Set of all sets of size l chosen from a PVK -/
noncomputable
def SSn := (Finset.univ : Finset (VK n)).powersetCard l.1
-- PROPERTIES
-- card = n choose l
theorem SSn_card :
(SSn n l).card = n.1.choose l.1 := by
  unfold SSn; simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
-- mem_card = l
@[local simp]
theorem SSn_mem_card :
∀(S : SSn n l), S.1.card = l.1 := by
  rintro ⟨S,hs⟩;unfold SSn at hs;grind only [= Finset.mem_powersetCard]
-- mem nonempty
instance (S : SSn n l) : Nonempty S := by
  have b0 := l.2
  rw [←SSn_mem_card n l S] at b0
  refine Finset.Nonempty.to_subtype ?_
  refine Finset.nonempty_of_ne_empty ?_
  by_contra cnt; grind only [= Finset.card_empty, cases eager Subtype]
/- =============================================== -/

/- =============================================== -/
/- Permutations of size l as Permutations -/
abbrev Permutation := Perm (Fin l.1)
-- PROPERTIES
-- card = l!
theorem Perm_univ_card :
Fintype.card (Permutation l) = l.1.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]
-- Nonempty
instance : Nonempty (Permutation l) := by
  exact Fintype.card_eq.mp rfl
/- =============================================== -/

/- =============================================== -/
/- Permutations of size l as Lists -/
structure PermList {n}{l} (S : SSn n l) where
  val : List S.1
  nodup : List.Nodup val
  len : val.length = l.1
-- PROPERTIES
-- finite
noncomputable
instance (S : SSn n l) : Fintype (PermList S) := by
  let T := {xs : List S // List.Nodup xs}
  refine Fintype.ofInjective
    ( fun (P : PermList S) ↦ (⟨P.1,P.2⟩ : T) )
    ( by
      simp only [Function.Injective, Subtype.mk.injEq]
      intro p1 p2 eq; obtain ⟨⟩ := p1; obtain ⟨⟩ := p2; simp_all only
    )
-- can decide mem = mem'
noncomputable
instance (S : SSn n l): DecidableEq (PermList S) := by
  exact Classical.typeDecidableEq (PermList S)
-- universe card = l! (PermList_univ_card ↓)
/- =============================================== -/

namespace Conv
/- =============================================== -/
/- # CONVERSIONS #
   Conversions handles mappings from the previously defined structures i.e.
   Permutation ↔ PermList
   PermList → Edgesets(representing Cycles)
   and provides relevant cardinalities -/
/- =============================================== -/

/- =============================================== -/
/- Maps values of l-size Vertexsets chosen from n vertices to indices-/
@[local grind]
private
def valToIdx (S : SSn n l): S.1 ↪ Fin l.1 :=
  ⟨fun s ↦ ( ⟨
    (S.1.sort (· ≤ ·)).idxOf (s : VK n)
    , by
    rw [←(SSn_mem_card n l S), @Nat.lt_iff_add_one_le]
    calc
      List.idxOf (↑s) (S.1.sort fun x1 x2 ↦ x1 ≤ x2) + 1
      _ ≤ (S.1.sort fun x1 x2 ↦ x1 ≤ x2).length := by {
        refine List.idxOf_lt_length_of_mem ?_
        simp only [Finset.mem_sort, SetLike.coe_mem]
      };
    rw [Finset.length_sort]
    ⟩ : Fin l.val)
    , by
    obtain ⟨S,Sp⟩ := S; intro a b heq ; simp_all only [Fin.mk.injEq]
    have nodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
    have t0 : (S.sort fun x1 x2 ↦ x1 ≤ x2).length = l.1 := by {
      rw [←SSn_mem_card n l ⟨S,Sp⟩]; simp only [Finset.length_sort]
    }
    set LSort := (S.sort fun x1 x2 ↦ x1 ≤ x2);
    set aidx := List.idxOf (↑a) LSort
    have at0 : aidx < LSort.length := by
      subst aidx; refine List.idxOf_lt_length_of_mem ?_
      subst LSort; simp only [Finset.mem_sort, SetLike.coe_mem]
    set bidx := List.idxOf (↑b) LSort
    have bt0 : bidx < LSort.length := by
      subst bidx;refine List.idxOf_lt_length_of_mem ?_
      subst LSort;simp only [Finset.mem_sort, SetLike.coe_mem]
    rw [←List.Nodup.getElem_inj_iff nodup] at heq
    · have t1 : LSort[aidx]'at0 = ↑a := by
        exact List.getElem_idxOf at0;
      have t2 : LSort[bidx]'bt0 = ↑b := by
        exact List.getElem_idxOf bt0;
      simp only [t1, t2, SetLike.coe_eq_coe] at heq
      assumption
    · trivial
    · trivial
  ⟩
/- =============================================== -/
/- Maps indices to values of l-size Vertex set chosen from n vertices -/
@[local grind]
private
def idxToVal (S : SSn n l): Fin l.1 ↪ S.1 :=
⟨ fun i ↦ ( ⟨
    (S.1.sort (· ≤ ·)).get (
      ⟨i,by simp only [Finset.length_sort, SSn_mem_card, Fin.is_lt]⟩
      : Fin (S.1.sort (· ≤ ·)).length )
    , by
    rw [← Finset.mem_sort (· ≤ ·)]
    apply List.get_mem
    ⟩ : S.1 )
  , by
  obtain ⟨S,sp⟩ := S
  intro a b heq; simp_all only [Subtype.mk.injEq]
  have h_nodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
  rw [List.Nodup.get_inj_iff h_nodup] at heq
  grind only
⟩
/- =============================================== -/
/- A bijection from values to indices and back -/
private
def idx_val {n}{l} (S : SSn n l) : Fin l.1 ≃ S.1 := {
  toFun := idxToVal n l S
  invFun := valToIdx n l S
  left_inv := by {
    intro s
    unfold valToIdx idxToVal; simp only [List.get_eq_getElem, Function.Embedding.coeFn_mk]
    obtain ⟨S,Sp⟩ := S; obtain ⟨n',s⟩ := s; simp only
    have nodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·);
    have : n' < (S.sort fun x1 x2 ↦ x1 ≤ x2).length := by
      simp;rw [SSn_mem_card n l ⟨S,Sp⟩];assumption
    rw [@Fin.mk_eq_mk]
    refine List.idxOf_getElem nodup n' this
  }
  right_inv := by {
    intro s
    unfold valToIdx idxToVal; simp only [List.get_eq_getElem, Function.Embedding.coeFn_mk,
      List.getElem_idxOf, Subtype.coe_eta]
  }
}
/- =============================================== -/

/- =============================================== -/
/- Embedding from Permutation to PermList. -/
def PermToPermList {n}{l} (S : SSn n l): Permutation l ↪ PermList S :=
  ⟨
    fun σ ↦ ⟨ --Permute Fin n then convert to values of S
      (List.ofFn σ.toFun).map (idx_val S).toFun
      , by -- Prove nodup
      refine List.Nodup.map ?_ ?_
      · simp only [toFun_as_coe]
        exact Equiv.injective _
      · simp only [toFun_as_coe]
        refine List.nodup_ofFn_ofInjective ?_
        exact Equiv.injective σ
      , by -- Prove len = l
      simp only [List.map_ofFn, List.length_ofFn]
      ⟩
    , by -- Prove injective
      simp only [List.map_ofFn]
      intro p1 p2 heq
      simp only [toFun_as_coe, PermList.mk.injEq, List.ofFn_inj] at heq
      apply (idx_val S).injective.comp_left at heq
      simp_all only [DFunLike.coe_fn_eq]
  ⟩
-- PROPERTIES
-- preserves length
@[local grind =, local simp]
theorem PermToPermList_len {n}{l} (S : SSn n l):
  ∀(σ : Permutation l), ((PermToPermList S).1 σ).1.length = S.1.card := by
  intro σ; unfold PermToPermList
  simp only [toFun_as_coe, List.map_ofFn, List.length_ofFn, SSn_mem_card]
-- preserves mem
theorem PermToPermList_mem_iff {n}{l} (S : SSn n l) :
  ∀(σ : Permutation l)(s : ↑S), s ∈ ((PermToPermList S).1 σ).1 := by
  intro p s; simp only [Function.Embedding.toFun_eq_coe]
  have t0 := PermToPermList_len S p
  simp only [Function.Embedding.toFun_eq_coe,SSn_mem_card] at t0
  rw [← List.mem_toFinset]
  have t1 :=
    Finset.eq_univ_of_card
    ((PermToPermList S) p).val.toFinset
    (
      by
      simp only [Fintype.card_coe]
      rw [←PermToPermList_len S p]
      simp only [Function.Embedding.toFun_eq_coe]
      refine List.toFinset_card_of_nodup ((PermToPermList S) p).nodup
    )
  rw [t1]; exact Finset.mem_univ s
-- surjective (PAIN)
theorem PermToPermList_surj {n}{l} (S : SSn n l): Function.Surjective (PermToPermList S) := by
  intro ⟨pl,plnodup,pllen⟩; unfold PermToPermList
  let F := idx_val S
  simp only [toFun_as_coe, List.map_ofFn, Function.Embedding.coeFn_mk, PermList.mk.injEq]
  have ⟨L,heq0⟩ : ∃(L : List (Fin l.1)), L.map F = pl := by {
    use pl.map F.2
    simp only [invFun_as_coe, List.map_map, self_comp_symm, List.map_id_fun, id_eq]
  };rw [←heq0]
  have Llen : L.length = l.1 := by
    grind only [
      = List.length_map, = List.nodup_iff_count,
      = List.nodup_iff_pairwise_ne, cases eager Subtype
    ];
  have ⟨σ,heq1⟩ : ∃(σ : Permutation l), List.ofFn σ = L := by {
    let f : Fin l.1 → Fin l.1 := fun i => L.get (⟨i,by grind⟩);
    have nodup : L.Nodup := by {
      rw [← List.nodup_map_iff F.injective]
      rw [heq0]; assumption
    }
    have f_inj : f.Injective := by {
      intro i j h
      simp [f] at h
      rw [L.nodup_iff_injective_get] at nodup
      exact (Fin.cast_inj (id (Eq.symm Llen))).mp (nodup h)
    }
    have f_bij : f.Bijective := by {
      exact Finite.injective_iff_bijective.mp f_inj
    }
    let σ : Permutation l := Equiv.ofBijective f f_bij
    use σ; simp only [List.get_eq_getElem, σ, f]
    convert List.ofFn_getElem L
    · simp only [Llen]
    · simp only [ofBijective_apply]; grind only [cases eager Subtype]
  }; rw [←heq1]; use σ
  simp only [List.map_ofFn, F]
-- bijective
theorem PermToPermList_bij {n}{l} (S : SSn n l) : (PermToPermList S).1.Bijective :=
  ⟨(PermToPermList S).injective,PermToPermList_surj S⟩
/- =============================================== -/

/- =============================================== -/
/- Embedding that maps an index i (bounded by l) to its successor neighbour -/
private
def succ : Fin l.1 ↪ Fin l.1 :=
  ⟨ fun a ↦ ⟨(a + 1) % l.1, by refine Nat.mod_lt (↑a + 1) ?_;have := l.2;linarith ⟩
  , by
    intro a b heq;ext;simp_all only [Fin.mk.injEq]
    have h (a : Fin l.val): (↑a + 1) % l.val = a.1 + 1 ∨ a.1 + 1 = l.val := by
      by_cases cs : a = l.1 - 1
      · right; rw [cs, Nat.sub_add_cancel]
        omega
      · left; have t : a + 1 < l.val := by omega
        exact Nat.mod_eq_of_lt t
    have ha := h a; have hb := h b
    obtain ha|ha := ha <;> obtain hb|hb := hb
    · rw [ha,hb] at heq; exact Nat.succ_inj.mp heq
    · rw [ha] at heq; simp only [hb, Nat.mod_self, Nat.add_eq_zero, one_ne_zero, and_false] at heq
    · rw [ha,hb] at heq; simp_all only [Nat.mod_self, Nat.right_eq_add, Nat.add_eq_zero,
      one_ne_zero, and_false]
    · linarith
  ⟩
-- PROPERTIES
-- values remain < l
private
lemma succ_lt_l : ∀(a : Fin l.1), succ l a < l.1 := by
  exact fun a ↦ ((succ l) a).isLt
-- values never equal
private
lemma succ_neq : ∀(a : Fin l.1), a ≠ succ l a := by
  intro a; unfold succ; simp only [Function.Embedding.coeFn_mk, ne_eq]
  have h : (↑a + 1) % l.val = a.1 + 1 ∨ a.1 + 1 = l.val := by
      by_cases cs : a = l.1 - 1
      · right; rw [cs, Nat.sub_add_cancel]
        omega
      · left; have t : a + 1 < l.val := by omega
        exact Nat.mod_eq_of_lt t
  apply Fin.ne_of_val_ne; simp only
  obtain h|h := h
  · rw [h];linarith
  · rw [h];simp only [Nat.mod_self, ne_eq];have := l.2;linarith
/- =============================================== -/

/- =============================================== -/
/- Given a Permlist, this is an Embedding from Fin l.1 to an edge, part of a Cycle -/
private
def idxToEK {n}{l}{S : SSn n l}(pl : PermList S) : Fin l.1 ↪ EK n :=
  ⟨ fun idx ↦
    let h0 : idx < pl.val.length := by rw [pl.3];exact idx.isLt;
    let h1 : ((succ l) idx) < pl.val.length := by rw [pl.3];exact succ_lt_l l idx;
    ⟨ --value
      s(pl.1[idx.1]'h0 , pl.1[succ l idx]'h1)
    , by -- proof that value is edge
      rw [mem_EK_iff];have nodup := pl.2
      by_contra cnt; simp only [Fin.getElem_fin, SetLike.coe_eq_coe] at cnt
      rw [List.Nodup.getElem_inj_iff
          nodup
          (i := idx.1) (j := (succ l) idx)] at cnt
      have := succ_neq l idx;apply this
      exact Fin.eq_of_val_eq cnt
    ⟩
  , by -- Proof it is injective
    simp only [Fin.getElem_fin]; intro a b heq; simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, SetLike.coe_eq_coe, Prod.swap_prod_mk] at heq
    obtain ⟨h0,h1⟩|⟨h0,h1⟩ := heq
    · rw [List.Nodup.getElem_inj_iff pl.nodup] at h0
      exact Fin.eq_of_val_eq h0
    · rw [List.Nodup.getElem_inj_iff pl.nodup] at h0
      rw [List.Nodup.getElem_inj_iff pl.nodup] at h1
      unfold succ at *; simp_all only [Function.Embedding.coeFn_mk, Nat.mod_add_mod]
      have := l.2
      have hb : b.val % l.val = b.val := Nat.mod_eq_of_lt b.is_lt
      nth_rw 2 [←hb] at h1
      symm at h1
      have h_dvd := Nat.ModEq.dvd h1
      simp only [Nat.cast_add, Nat.cast_one] at h_dvd
      rw [add_assoc,add_sub_assoc,add_sub_cancel] at h_dvd
      simp only [Int.reduceAdd] at h_dvd
      have h_le_2 : l.val ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact Int.ofNat_dvd.mp h_dvd)
      linarith
  ⟩
/- =============================================== -/
/- Given a Permlist, this will give us the corresponding PEC (Cycle Edgeset) -/
private
def idxToPEK {n}{l}{S : SSn n l}(pl : PermList S) : PEK n :=
  (Finset.univ : Finset (Fin l.1)).map (idxToEK pl)
-- PROPERTIES :
-- The PEC (Cycle) returned has length l
private
theorem idxToPEK_Card {n}{l}(S : SSn n l) :
  ∀(pl : PermList S), (idxToPEK pl).ncard = l.1 := by
  intro pl;unfold idxToPEK
  rw [@Set.ncard_coe_finset, Finset.card_map]
  rw [Finset.card_univ, Fintype.card_fin]
/- =============================================== -/
end Conv

/- =============================================== -/
/- Function from PermList to Cycle Edgesets -/
def PermListToPEK {n}{l}(S : SSn n l) : PermList S → PEK n := Conv.idxToPEK
-- PROPERTIES
-- The PEC (Cycle) returned has length l
theorem PermListToPEK_Card {n}{l} (S : SSn n l) :
  ∀(pl : PermList S), ((PermListToPEK S) pl).ncard = l.1 := by
  intro pl; unfold PermListToPEK;apply Conv.idxToPEK_Card
/- =============================================== -/

/- =============================================== -/
/- # Various Theorems #
   Theorems that needed future lemmas or definitions in order to be proven.
   They are thus here at the end of this section. -/
/- =============================================== -/
/- =============================================== -/
/- PROPERTY of PermList:
   card = l! -/
theorem PermList_univ_card {n}{l}(S : SSn n l) :
Fintype.card (PermList S) = l.1.factorial := by
  rw [←Perm_univ_card]; symm
  refine Fintype.card_congr
    (Equiv.ofBijective
      (Conv.PermToPermList S)
      (Conv.PermToPermList_bij S)
    )
/- =============================================== -/
end Defs

/- Create a k to 1 mapping from PermList 1 to Edgesets.
   We have Finset.card_eq_mul_card_image_of_forall_card_fiber_eq that then gives us l! / (2l)
-/
/- =============================================== -/
/- # kToOne #
   This section will prove that idxToPEC is a kTo1 mapping from PermLists to Cyclesets.
   (Cycles of length l)
   More exactly that idxToPEC maps 2l PermLists to exactly one PEC, a.k.a Cycle.
   This section concludes with the theorem that there are exactly l!/2l possible cycles. -/
/- =============================================== -/

/- =============================================== -/
/- Rotational relation -/
abbrev RotationalRel {n}{l}{S : SSn n l}(pl1 pl2 : PermList S):=
  ∃(k : Fin l.1), pl1.1.rotate k.1 = pl2.1
-- decidable
instance (S : SSn n l): DecidableRel (fun pl1 pl2 : PermList S ↦ (RotationalRel pl1 pl2)) := by
  infer_instance
-- Helper
private
lemma arith0 {l : Cval}(k : ℕ) : k % l.1 < l.1 := by
  have:=l.2;refine Nat.mod_lt k (by omega)
/- =============================================== -/
/- RotationalListSetoid -/
private
def RotationalListSetoid {n}{l}(S : SSn n l) : Setoid (PermList S) where
  r := RotationalRel
  iseqv := {
    refl := by
      intro pl; unfold RotationalRel; use ( ⟨0,by have := l.2;linarith⟩ : Fin l.1 )
      exact List.rotate_zero _
    symm := by
      intro pl1 pl2; unfold RotationalRel; intro ⟨k,heq⟩; rw [←heq]
      by_cases cs : k.1 = 0
      · rw [cs]
        use ⟨0,by have:=l.2;omega⟩
        simp only [List.rotate_zero]
      · have t0 : 0 < k.1 := by omega
        use ⟨l.1 - k,by have:=l.2;omega⟩
        refine List.ext_getElem ?_ ?_
        · simp only [List.length_rotate]
        · intro idx h1 h2
          rw [ List.getElem_rotate, List.getElem_rotate ]
          simp only [List.length_rotate, Nat.mod_add_mod]
          congr
          rw [add_assoc,Nat.sub_add_cancel (by omega), pl1.3,
            Nat.add_mod_right, ←pl1.3 ,Nat.mod_eq_of_lt h2]
    trans := by
      intro pl1 pl2 pl3; unfold RotationalRel; intro ⟨k1,heq1⟩ ⟨k2,heq2⟩
      rw [←heq2,←heq1]; use ⟨(k1.1 + k2.1)%l.1,by
        have:=l.2;refine Nat.mod_lt (↑k1 + ↑k2) ?_;omega⟩
      simp only;
      rw[List.rotate_rotate pl1.1 k1.1 k2.1]; simp only [←pl1.3]; rw [List.rotate_mod pl1.1]
  }
/- =============================================== -/
/- Equivalence Class of PermLists with RotationalRel -/
abbrev RotationalList {n}{l}(S : SSn n l) := Quotient (RotationalListSetoid S)
-- Properties
-- finite
noncomputable
instance {n}{l}(S : SSn n l) : Fintype (RotationalList S) := by
  exact Fintype.ofFinite (RotationalList S)
-- decidable
noncomputable
instance {n}{l}(S : SSn n l) : DecidableEq (RotationalList S) := by
  exact Classical.typeDecidableEq (RotationalList S)
-- predicate is decidable
noncomputable
instance {n}{l}{S : SSn n l}(rl : RotationalList S): DecidablePred (fun t ↦ ⟦t⟧ = rl) := by
  exact Classical.decPred fun t ↦ ⟦t⟧ = rl
-- mem card = l
  -- embedding from fin l to Rotational List
  noncomputable
  def kToRotationalList {n}{l}(S : SSn n l) (rl : RotationalList S):
    (Finset.univ : Finset (Fin l.1)) ↪
    {pl : PermList S | Quotient.mk (RotationalListSetoid S) pl = rl} :=
    ⟨ fun k ↦ ⟨(
        ⟨rl.out.1.rotate k.1,
        by
        set pl' := (Quotient.out rl)
        have := pl'.nodup
        exact List.nodup_rotate.mpr this
        ,
        by
        set pl' := (Quotient.out rl)
        simp only [ ← pl'.3, List.length_rotate]
        ⟩ : PermList S ),
        by
        rw [@Set.mem_setOf_eq];rw [Quotient.mk_eq_iff_out]
        simp only [HasEquiv.Equiv, RotationalListSetoid, RotationalRel]
        by_cases cs : k.1.1 = 0
        · rw [cs]; use ⟨0,by omega⟩
          simp only [List.rotate_zero]
        · use ⟨l.1 - k.1.1, by omega⟩
          simp only
          rw [List.rotate_rotate, Nat.add_sub_cancel' (by omega)]
          rw [← @List.rotate_mod,(Quotient.out rl).3,Nat.mod_self,List.rotate_zero]
        ⟩
    , by
      intro a b; simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, PermList.mk.injEq]
      intro heq
      apply List.Nodup.rotate_congr (Quotient.out rl).2 at heq
      pick_goal 2;{
      have t1 := (Quotient.out rl).3; have t0 := l.2; by_contra
      simp_all only [List.rotate_nil,List.length_nil]; rw [←t1] at t0
      contradiction }
      rw [(Quotient.out rl).3,Nat.mod_eq_of_lt a.1.2,Nat.mod_eq_of_lt b.1.2] at heq
      grind only [← Finset.mem_univ, cases eager Subtype, cases Or]
    ⟩
  -- PROPERTIES
  -- surjective
  theorem kToRotationalList_surj {n}{l}(S : SSn n l) (rl : RotationalList S) :
  Function.Surjective (kToRotationalList S rl) := by
  intro ⟨pl,hp⟩; unfold kToRotationalList
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Function.Embedding.coeFn_mk, Subtype.mk.injEq]
  simp only [Set.mem_setOf_eq] at hp
  rw [Quotient.mk_eq_iff_out] at hp
  simp only [HasEquiv.Equiv, RotationalListSetoid, RotationalRel] at hp
  obtain ⟨k,hp⟩ := hp
  by_cases cs : k.1 = 0
  · rw [cs] at hp; simp only [List.rotate_zero] at hp
    simp only [←hp]; use ⟨⟨0,by omega⟩,by simp only [Finset.mem_univ]⟩
    simp only [List.rotate_zero]
  · use ⟨⟨l.1 - k,by omega⟩,by simp only [Finset.mem_univ]⟩
    simp only [← hp,List.rotate_rotate]
    simp only [Fin.is_le', add_tsub_cancel_of_le]
    have : pl.val.rotate l.1 = pl.1 := by rw [←pl.3];rw [@List.rotate_length]
    simp only [this]
  -- bijective
  theorem kToRotationalList_bij {n}{l}(S : SSn n l) (rl : RotationalList S) :
  Function.Bijective (kToRotationalList S rl) :=
  ⟨(kToRotationalList S rl).2,kToRotationalList_surj S rl⟩
-- MEM CARD = l
theorem RotationalList_mem_card' {n}{l}(S : SSn n l) :
∀(rl : RotationalList S),
  Fintype.card
  {pl : PermList S | Quotient.mk (RotationalListSetoid S) pl = rl} = l.1 := by
  intro rl
  apply rl.ind
  intro pl
  have t : (Finset.univ : Finset (Fin l.1)).card = l.1 := by exact Finset.card_fin l.val
  rw [← t]; symm
  refine Finset.card_eq_of_equiv_fintype ?_
  refine Equiv.ofBijective (kToRotationalList S ⟦pl⟧) (kToRotationalList_bij S ⟦pl⟧)
theorem RotationalList_mem_card {n}{l}(S : SSn n l) :
∀(rl : RotationalList S),
  {pl : PermList S | Quotient.mk (RotationalListSetoid S) pl = rl}.toFinset.card = l.1 := by
  intro rl
  rw [@Set.toFinset_card];exact RotationalList_mem_card' S rl
-- card = l! / l
theorem RotationalList_univ_card {n}{l}(S : SSn n l) :
  Fintype.card (RotationalList S) = l.1.factorial / l.1 := by
  have mapsTo : Set.MapsTo
    (Quotient.mk (RotationalListSetoid S) )
    (Finset.univ : Finset (PermList S))
    (Finset.univ : Finset (RotationalList S)) := by
    simp only [Finset.coe_univ, Set.mapsTo_univ_iff, Set.mem_univ, implies_true];
  have card := Finset.card_eq_sum_card_fiberwise mapsTo
  rw [show Finset.univ.card = l.1.factorial from
    by simp only [Finset.card_univ]; rw [PermList_univ_card]
    ] at card
  have h : ∀b ∈ (Finset.univ : Finset (RotationalList S)),
    (fun b ↦ {a | ⟦a⟧ = b}.toFinset.card) b = (fun _ ↦ l.1) b := by
      intro b; simp only [Finset.mem_univ, Set.toFinset_setOf, forall_const]
      convert (RotationalList_mem_card' S b)
      exact
        Eq.symm
          (Fintype.card_ofFinset (Finset.filter (Membership.mem {pl | ⟦pl⟧ = b}) Finset.univ)
            (Subtype.fintype._proof_1 (Membership.mem {pl | ⟦pl⟧ = b})))
  have bruh :
    (Finset.univ : Finset (RotationalList S)) = (Finset.univ : Finset (RotationalList S)) :=
    by rfl
  have sumcong := Finset.sum_congr (bruh) (h)
  simp only [Set.toFinset_setOf, Finset.sum_const, Finset.card_univ, smul_eq_mul] at sumcong
  rw [sumcong] at card; rw [card, Nat.mul_div_assoc (Fintype.card (RotationalList S)) (by simp)]
  rw [Nat.div_self, Nat.mul_one]
  have := l.2; linarith
/- =============================================== -/
/- map Rotational List to PEK (Lifting function) -/
def toPEK {n}{l}{S : SSn n l}(rl : RotationalList S) :=
  Quotient.lift
  ( fun pl ↦ (PermListToPEK S) pl )
  ( by
    intro pl1 pl2 heq
    simp only [PermListToPEK, Conv.idxToPEK, Conv.idxToEK]
    simp [HasEquiv.Equiv, RotationalListSetoid, RotationalRel] at heq
    obtain ⟨k,heq⟩ := heq
    ext e
    simp only [Fin.getElem_fin, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ,
      Set.image_univ, Set.mem_range]
    constructor
    · simp only [forall_exists_index]
      unfold Conv.succ; simp only [Function.Embedding.coeFn_mk]
      intro idx h; rw [←h]
      simp only [← heq, Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, SetLike.coe_eq_coe,
        Prod.swap_prod_mk]
      use ⟨(l.1 + idx - k) % l.1,
        by refine Nat.mod_lt (l.val + ↑idx - ↑k) ?_;have:=l.2;omega⟩
      left; simp only [Nat.mod_add_mod]
      constructor
      · rw [List.getElem_rotate]; simp only [pl1.3, Nat.mod_add_mod]
        congr
        rw [Nat.sub_add_cancel (by omega), Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      · rw [List.getElem_rotate]; simp only [pl1.3, Nat.mod_add_mod]
        conv =>
          enter[1,2];rw [add_assoc,add_comm 1,←add_assoc]
          rw [Nat.sub_add_cancel (by omega),add_assoc,Nat.add_mod_left]
    · simp only [forall_exists_index]
      unfold Conv.succ; simp only [Function.Embedding.coeFn_mk]
      intro idx h; rw [←h]
      simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, SetLike.coe_eq_coe,
        Prod.swap_prod_mk, ←heq]
      use ⟨(idx + k) % l.1,
        by refine Nat.mod_lt _ ?_;have:=l.2;omega⟩
      left; simp only [Nat.mod_add_mod]
      constructor
      · rw [List.getElem_rotate];simp only [pl1.3]
      · rw [List.getElem_rotate];simp only [pl1.3]; simp only [Nat.mod_add_mod]
        conv => enter [1,2];rw [add_assoc,add_comm k.1,←add_assoc]
  )
  rl
/- =============================================== -/
/- reverse -/
noncomputable
def reverse {n}{l}{S : SSn n l}(rl : RotationalList S) :=
  Quotient.mk (RotationalListSetoid S)
  ⟨
    rl.out.1.reverse,
    by simp only [List.nodup_reverse, (Quotient.out rl).2],
    by simp only [List.length_reverse, (Quotient.out rl).3]
  ⟩
-- PROPERTIES
-- The reverse of a RotationalList is never equals to itself
theorem reverse_ne {n}{l}{S : SSn n l}(rl : RotationalList S) :
  rl ≠ reverse rl := by {
    unfold reverse
    by_contra cnt
    rw [Quotient.eq_mk_iff_out] at cnt
    simp [HasEquiv.Equiv,RotationalListSetoid,RotationalRel] at cnt
    revert cnt; simp only [imp_false, not_exists]

    have no_rotate (L : PermList S) : ∀(k : Fin l.1),
    L.1.rotate ↑k ≠ L.1.reverse := by {
      intro k heq
      rw [List.ext_get_iff] at heq
      simp only [List.length_rotate, List.length_reverse, List.get_eq_getElem, List.getElem_reverse,
        true_and,L.3] at heq
      obtain ⟨L,nodup,len⟩ := L
      simp only at heq
      have mycongr (i j : Fin l.1) : L[i] = L[j] → i = j := by
        rw [List.nodup_iff_injective_getElem] at nodup
        unfold Function.Injective at nodup
        simp only at nodup
        intro he
        let i' : Fin L.length := ⟨i.1,by omega⟩
        let j' : Fin L.length := ⟨j.1,by omega⟩
        have ijeq : L[i'] = L[j'] := by
          subst i' j'; simp_all only [Fin.getElem_fin]
        specialize (nodup ijeq); subst i' j';
        obtain ⟨i,ip⟩ := i; obtain ⟨j,jp⟩ := j
        simp_all only [Fin.getElem_fin, Fin.mk.injEq]
      by_cases cs : k.1 = l.1 - 1
      · rw [cs] at heq
        have := l.2
        specialize (heq 1 (by omega) (by omega))
        rw [L.getElem_rotate] at heq
        rw [←Nat.add_sub_assoc (by omega),
            Nat.add_sub_cancel_left] at heq
        simp only [len, Nat.mod_self] at heq
        let zero : Fin l.1 := ⟨0,by linarith⟩
        let lval : Fin l.1 := ⟨l.1 - 1 - 1,by omega⟩
        specialize (mycongr zero lval heq)
        subst zero lval; simp only [Fin.mk.injEq] at mycongr
        omega
      · specialize (heq 0 (by have:=k.2;omega) (by have:=k.2;omega))
        rw [L.getElem_rotate] at heq
        simp only [zero_add, tsub_zero, len, Nat.mod_eq_of_lt k.2] at heq
        let lval : Fin l.1 := ⟨l.1 - 1,by have:=l.2;omega⟩
        specialize (mycongr k lval); subst lval; simp at mycongr
        specialize (mycongr heq)
        obtain ⟨k,kp⟩ := k
        simp only [Fin.mk.injEq] at mycongr
        simp_all only [not_true_eq_false]
    }

    intro k
    intro h
    specialize (no_rotate (Quotient.out rl) k)
    contradiction
  }
/- =============================================== -/

/- =============================================== -/
/- Cycle equivalence relation -/
abbrev PermListRel {n}{l}{S : SSn n l}(rl1 rl2 : RotationalList S) :=
  rl1 = rl2 ∨ ∀pl, Quotient.mk (RotationalListSetoid S) pl = rl1 ↔
  Quotient.mk (RotationalListSetoid S) ⟨
          pl.1.reverse,
          by have:=pl.2;exact List.nodup_reverse.mpr this,
          by have:=pl.3;rw[←this];exact List.length_reverse
          ⟩ = rl2
/- =============================================== -/
/- Cycle Setoid -/
private
def CycleSetoid {n}{l}(S : SSn n l) : Setoid (RotationalList S) where
  r := PermListRel
  iseqv := {
    refl := by
      intro rl; unfold PermListRel; left; rfl
    symm := by
      intro rl1 rl2; unfold PermListRel
      rintro (pre|pre)
      · left; exact pre.symm
      · right; intro pl
        set prev : PermList S := ⟨pl.val.reverse, _,_⟩
        specialize (pre prev); rw [pre]
        simp only [List.reverse_reverse, prev]
    trans := by
      grind only [= List.reverse_reverse, = List.nodup_iff_count, = List.pairwise_reverse,
        = List.nodup_iff_pairwise_ne, = List.length_reverse, → List.Pairwise.isChain,
        cases eager Subtype, cases Or]
  }
/- =============================================== -/
/- Equivalence Class of Cycles over Rotational List-/
abbrev Cycle {n}{l}(S : SSn n l) := Quotient (CycleSetoid S)
-- finite
noncomputable
instance {n}{l}(S : SSn n l) : Fintype (Cycle S) := by
  exact Fintype.ofFinite (Cycle S)
-- mem card = 2
  -- embedding from bool to Rotational List
  noncomputable
  def boolToCycle {n}{l}(S : SSn n l) (C : Cycle S) :
  (Finset.univ : Finset Bool) ↪
  {rl : RotationalList S | Quotient.mk (CycleSetoid S) rl = C} :=
  ⟨ fun b ↦
      if b then ⟨C.out,by simp only [Set.mem_setOf_eq, Quotient.out_eq]⟩
           else ⟨reverse (C.out),by
             simp only [Quotient.mk_eq_iff_out, reverse, Set.mem_setOf_eq]
             simp only [HasEquiv.Equiv,CycleSetoid,PermListRel]
             right
             intro pl
             constructor
             · simp only [Quotient.eq, RotationalListSetoid,RotationalRel]
               intro ⟨k,h⟩
               simp only [Quotient.mk_eq_iff_out,HasEquiv.Equiv, RotationalRel]
               rw [(List.reverse_eq_iff).symm] at h
               rw [List.reverse_rotate, pl.3] at h
               by_cases cs : k.1 = 0
               · rw [←h,cs]; simp only [Nat.zero_mod, tsub_zero]
                 use ⟨0,by omega⟩
                 have : pl.val.reverse.length = l.1 := by
                  rw[←pl.3];exact List.length_reverse
                 simp only [←this]; rw [List.rotate_length, List.rotate_zero]
               · use ⟨l.val - ↑k % l.val,
                  by
                  rw [Nat.mod_eq_of_lt (by omega)]
                  omega ⟩
             · simp only [Quotient.eq, RotationalListSetoid,RotationalRel]
               simp only [Quotient.mk_eq_iff_out,HasEquiv.Equiv, RotationalRel]
               intro ⟨k,h⟩; rw [←h]
               rw [List.reverse_rotate,List.reverse_reverse]
               rw [show pl.val.reverse.length = l.1 from
                by rw [←pl.3];exact List.length_reverse ]
               by_cases cs : k.1 = 0
               · rw [cs]; simp only [Nat.zero_mod, tsub_zero]
                 use ⟨0,by omega⟩
                 simp only [List.rotate_zero, ← pl.3, List.rotate_length]
               · use ⟨(l.val - ↑k % l.val),by
                  rw [Nat.mod_eq_of_lt (by omega)]
                  omega
                  ⟩
            ⟩
  , by
    intro b1 b2
    fin_cases b1, b2
    · simp only [Set.coe_setOf, ↓reduceIte, Set.mem_setOf_eq, Fintype.univ_bool, Finset.insert_val,
      Finset.singleton_val, imp_self]
    · intro heq; exfalso; simp at heq
      have := reverse_ne (Quotient.out C)
      contradiction
    · intro heq; exfalso; simp at heq
      have := reverse_ne (Quotient.out C)
      symm at this
      contradiction
    · simp only [Set.coe_setOf, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq,
      Fintype.univ_bool, Finset.insert_val, Finset.singleton_val, imp_self]
  ⟩
  -- surjective (Refreshingly not painful)
  theorem boolToCycle_surj {n}{l}(S : SSn n l) (C : Cycle S) :
    Function.Surjective (boolToCycle S C) := by
    intro ⟨rl,hp⟩
    unfold boolToCycle reverse; simp only [Fintype.univ_bool, Set.coe_setOf, Set.mem_setOf_eq,
      Function.Embedding.coeFn_mk, Subtype.exists, Finset.mem_insert, Finset.mem_singleton,
      Bool.eq_true_or_eq_false_self, exists_true_left, Bool.exists_bool, Bool.false_eq_true,
      ↓reduceIte]
    simp only [Set.mem_setOf_eq] at hp
    rw [Quotient.mk_eq_iff_out] at hp
    simp only [HasEquiv.Equiv, CycleSetoid,PermListRel] at hp
    obtain hp|hp := hp
    · right; simp only [Subtype.mk.injEq]
      exact id (Eq.symm hp)
    · left
      simp only [Subtype.mk.injEq, hp, List.reverse_reverse]
      rw [Quotient.mk_eq_iff_out]
      simp only [HasEquiv.Equiv, RotationalListSetoid, RotationalRel]
      use ⟨0,by have:=l.2;omega⟩
      simp only [List.rotate_zero]
  -- bijective
  theorem boolToCycle_bij {n}{l}(S : SSn n l) (C : Cycle S) :
  Function.Bijective (boolToCycle S C) := ⟨(boolToCycle S C).2,boolToCycle_surj S C⟩
/- === -/
  -- helper instance
  noncomputable
  instance {n}{l}(S : SSn n l)(C : Cycle S):
    Fintype ({rl : RotationalList S | Quotient.mk (CycleSetoid S) rl = C}) := by
    exact Fintype.ofFinite ↑{rl | ⟦rl⟧ = C}
-- MEM CARD = 2
theorem Cycle_mem_card' {n}{l}(S : SSn n l) :
∀(C : Cycle S),
  Fintype.card
  {rl : RotationalList S | Quotient.mk (CycleSetoid S) rl = C} = 2 := by
  intro C
  apply C.ind
  intro rl'
  have t : (Finset.univ : Finset Bool).card = 2 := by
    exact rfl
  rw [← t]; symm
  refine Finset.card_eq_of_equiv_fintype ?_
  refine Equiv.ofBijective (boolToCycle S ⟦rl'⟧) (boolToCycle_bij S ⟦rl'⟧)
-- card = l! / (2l)
theorem Cycle_univ_card {n}{l}(S : SSn n l) :
  Fintype.card (RotationalList S) = l.1.factorial / (2*l.1) := by
  sorry
/- =============================================== -/

section Probability
/- =============================================== -/
/- # Probability #
   This section wraps up, by providing the desired theorem for the main proof. -/
/- =============================================== -/
-- [TODO]
end Probability

end API_ℂ
