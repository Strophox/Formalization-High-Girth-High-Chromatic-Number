import Mathlib
import Formalization.API_Probability

set_option autoImplicit false
set_option linter.style.commandStart false
set_option linter.style.induction false
variable {α : Type*}

open API_ℙ
open scoped API_ℙ
variable (n : Nval)
variable (p : ℙval)
namespace API_ℂ
register_simp_attr API_C

/- # Values # -/
/- Length of a cycle must be ≥ 3 -/
structure CycVal where
  val : ℕ
  proof : 3 ≤ val
variable (l : CycVal)

/- =============================================== -/
namespace Defs

/- # Defs # -/
/- Define a cycle using permutations -/
structure Permutation where
  val : List (VK n)
  proof : List.Nodup val
-- Properties :
noncomputable instance : DecidableEq (Permutation n) := by -- is Decidable
  exact Classical.typeDecidableEq (Permutation n)
instance : Fintype (Permutation n) := by -- is FinType
  let T := { l : List (VK n) // l.Nodup };
  let f1: Permutation n → T := fun s ↦ ⟨s.1,s.2⟩
  let f2 : T → Permutation n := fun s ↦ ⟨s.1,s.2⟩
  apply Fintype.ofEquiv T
  constructor
  pick_goal 4;{use f1}
  pick_goal 3;{use f2}
  · exact congrFun rfl
  · exact congrFun rfl

/- =============================================== -/

/- # Conversions # -/
/- Helpers -/
private lemma nodup_step : ∀(a : VK n)(L : List (VK n)), (a :: L).Nodup → L.Nodup := by
  intros a L h
  obtain ⟨⟩ := h
  unfold List.Nodup; assumption
/- Turns CycleDef(Permutation) into PathDef(Edgeset) HELPER -/
private def Perm_to_Edgeset : Permutation n → PEK n
 | ⟨[],_⟩       => {}
 | ⟨_::[],_⟩    => {}
 | ⟨_::_::[],_⟩ => {}
 | ⟨a::b::c::S,p⟩ =>
    let e1 : EK n := ⟨s(a,b),by simp_all⟩;
    let e2 : EK n := ⟨ s(b,c),by apply nodup_step at p;simp_all⟩;
    insert e1 (insert e2 (Perm_to_Edgeset ⟨c::S,by grind⟩))

/- Turns CycleDef(Permutation) into CycleDef(Edgeset)-/
def Perm_to_Cycset (S : Permutation n) : PEK n :=
  match S with
  | ⟨[],_⟩       => {}
  | ⟨_::[],_⟩    => {}
  | ⟨_::_::[],_⟩ => {}
  | ⟨a::b::c::L,p⟩ =>
    let z : VK n := (a::b::c::L).getLast (by exact List.cons_ne_nil a _);
    let e : EK n := ⟨s(a,z),by rw [mem_EK_iff];grind⟩;
    insert e (Perm_to_Edgeset n S)

/- Small sanity checks -/
private example :
Perm_to_Cycset ⟨5,by linarith⟩ ⟨[0,4,2],by exact List.dedup_eq_self.mp rfl⟩
= { ⟨Sym2.mk (0,4),by simp⟩, ⟨Sym2.mk (4,2),by simp⟩, ⟨Sym2.mk (0,2),by simp⟩} := by
  simp [Perm_to_Cycset, Perm_to_Edgeset]
  grind only [= Set.subset_def, usr Set.subset_insert, = Set.singleton_subset_iff,
    = Set.mem_insert_iff, = Set.mem_singleton_iff, cases eager Subtype, cases Or]
private example :
Perm_to_Cycset ⟨3,by linarith⟩ ⟨[0,2],by exact List.dedup_eq_self.mp rfl⟩ = ∅ := by
  simp [Perm_to_Cycset]

/- # Cycle Equivalence Class # -/
/- The euqivalence relation -/
abbrev CycEq (C1 C2 : Permutation n) :=
  List.IsRotated C1.1 C2.1 ∨ List.IsRotated C1.1 C2.1.reverse
/- The cycle type is a set of equivalence classes over permutations over Fin n
   An instance of an setoid(Equivalence class) is declared first... -/
instance PermutationSetoid : Setoid (Permutation n) where
  r := CycEq n
  iseqv := {
    refl := by intro C; simp_all [CycEq];left;trivial
    symm := by {
      intro C1 C2 h; simp_all only [CycEq]
      obtain h|h := h
      · left;exact id (List.IsRotated.symm h)
      · right;exact List.isRotated_reverse_comm_iff.mp (id (List.IsRotated.symm h))
    }
    trans := by {
      intro C1 C2 C3 h0 h1
      simp_all [CycEq]
      obtain h0|h0 := h0
      · obtain h1|h1 := h1
        · left;exact List.IsRotated.trans h0 h1
        · right;exact List.IsRotated.trans h0 h1
      · obtain h1|h1 := h1
        · right
          rw [← List.isRotated_reverse_comm_iff]
          rw [← List.isRotated_reverse_comm_iff] at h0
          exact List.IsRotated.trans h0 h1
        · left
          rw [← List.isRotated_reverse_comm_iff] at h1
          exact List.IsRotated.trans h0 h1
    }
  }

/- That setoid is turned into a type giving a equivalence class type -/
def Cycle := Quotient (PermutationSetoid n)
-- Properties
noncomputable instance : Fintype (Cycle n) := by
  unfold Cycle; exact Fintype.ofFinite (Quotient (PermutationSetoid n))

/- LEMMAS -/
@[local grind .]
private lemma Cycle_len_eq_iff (C1 C2 : Permutation n) :
  C1 ≈ C2 → C1.1.length = C2.1.length := by {
    intros heq; obtain heq|heq := heq
    · simp only [List.IsRotated] at heq
      obtain ⟨k,heq⟩ := heq
      have : (C1.1.rotate k).length = (C2.1).length :=
        by exact congrArg List.length heq
      calc
        C1.1.length
        _ = (C1.1.rotate k).length := by exact Eq.symm (List.length_rotate C1.1 k)
        _ = C2.1.length := by exact this
    · simp only [List.IsRotated] at heq
      obtain ⟨k,heq⟩ := heq
      have : (C1.val.rotate k).length = (C2.val.reverse).length :=
        by exact congrArg List.length heq
      calc
        C1.val.length
        _ = (C1.1.rotate k).length := by exact Eq.symm (List.length_rotate C1.val k)
        _ = C2.1.reverse.length := by exact this
        _ = C2.1.length := by exact List.length_reverse
  }
@[local grind .]
private lemma Cycle_Edgeset_eq_iff (C1 C2 : Permutation n) :
  C1 ≈ C2 → Perm_to_Cycset n C1 = Perm_to_Cycset n C2
  := by {
    obtain ⟨c1,c1p⟩ := C1; obtain ⟨c2,c2p⟩ := C2
    intro heq; obtain heq|heq := heq
    all_goals (simp only [List.IsRotated] at heq; obtain ⟨k,heq⟩ := heq)
    · match c1 with
      | [] => simp only [←heq, List.rotate_nil]
      | [a] => simp only [←heq, Perm_to_Cycset, List.rotate_singleton]
      | [a,b] => {
        have t0 : c2.length = 2 := by {
          have : ([a, b].rotate k).length = 2 := by simp only [List.length_rotate, List.length_cons,
            List.length_nil, zero_add, Nat.reduceAdd]
          simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
            not_false_eq_true, List.nodup_nil, and_self, and_true]
        }
        have : c2 = [a,b] ∨ c2 = [b,a] := by
          rw [List.rotate_eq_iff] at heq
          simp only [t0] at heq
          have t : (2 - k % 2) = 1 ∨ (2 - k % 2) = 2 := by omega
          obtain t|t := t
          · right; simp only [t] at heq
            have t' : [b,a].rotate 1 = [a,b] := by simp only [List.rotate_cons_succ,
              List.cons_append, List.nil_append, List.rotate_zero]
            rw [←t'] at heq
            exact List.rotate_eq_rotate.mp (id (Eq.symm heq))
          · left; simp only [t] at heq
            have t' : [a,b].rotate 2 = [a,b] := by
              simp only [List.rotate_cons_succ, List.cons_append,
              List.nil_append, List.rotate_zero]
            rw [←t']; simp_all only [List.nodup_rotate, List.rotate_eq_rotate]
        obtain cs|cs := this
        · simp only [cs]
        · simp only [cs]
          simp only [Perm_to_Cycset]
      }
      | a::b::c::S => {
        sorry
      }
    · sorry
  }

/- # Lifting Functions # -/
/- Size of Cycle -/
noncomputable def Cycle_len ( S : Cycle n ) : ℕ :=
  Quotient.lift
    (fun s ↦ if s.1.length ≥ 3 then s.1.length else 0)
    (by intro S1 S2 h; grind only [Cycle_len_eq_iff, cases Or])
    S

/-  Edgeset of Cycle -/
noncomputable def Cycle_toEdgeset ( S : Cycle n ) : PEK n :=
  Quotient.lift
    (fun s ↦ Perm_to_Cycset n s)
    (by grind)
    S

/- A subtype containing only cycles of a certain length -/
def CycleOfL := { (C : (Cycle n)) | Cycle_len n C = l.1}
-- Properties :
noncomputable instance : Fintype (CycleOfL n l) := by
  unfold CycleOfL; exact setFintype {C | Cycle_len n C = l.val}

end Defs
/- =============================================== -/

namespace Theorems
open Defs

/- # Theorems # -/

/- # ..Cycles # -/
/- TODO: Prove that there are exactly n choose k cycles of length l in a graph of size n
   NOTE that l is forced to be ≥3 !! This might be extremely hard :( -/
theorem CycleOfL_card : (CycleOfL n l).toFinset.card =
  Nat.choose n.1 l.1 * (Nat.factorial l.1) / (2 * l.1) := by sorry

/- # ..Probability i.e. 𝔼/ℙ # -/
/- The expected number of cycles with length l-/
noncomputable def E_CycleOfL := ∑(C : CycleOfL n l), Pr_EsubG p n (Cycle_toEdgeset n C)

/- TODO: Prove that 𝔼[#cycles with length l] = n choose k * p^l -/
theorem Cycset_eq_card :
  E_CycleOfL n p l = (CycleOfL_card n l) * (p.1^l.1 : ℝ) := by sorry

end Theorems

end API_ℂ
