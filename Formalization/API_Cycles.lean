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

/- # Values # -/
/- Length of a cycle must be ≥ 3 -/
structure CycVal where
  val : ℕ
  proof : 3 ≤ val
variable (l : CycVal)

/- =============================================== -/

/- # Defs # -/
/- Define a cycle using permutations -/
def Permutation := { (S : List (VK n)) | List.Nodup S}
-- Properties :
noncomputable instance : DecidableEq (Permutation n) := by
  exact Classical.typeDecidableEq (Permutation n)
instance : Fintype (Permutation n) := by
  refine Fintype.ofEquiv { S : List (VK n) // List.Nodup S} (by rfl)
/- =============================================== -/

/- # Conversions # -/
/- Turns CycleDef(Permutation) into PathDef(Edgeset) -/
private def Permut_to_Edgeset : Permutation n → PEK n
 | ⟨[],_⟩       => {}
 | ⟨a::[],_⟩    => {}
 | ⟨a::b::s,_⟩  => {⟨Sym2.mk (a, b),by simp_all [Permutation]⟩}
                    ∪ Permut_to_Edgeset ⟨b::s,by simp_all [Permutation]⟩
/- Small sanity check -/
private example :
Permut_to_Edgeset ⟨3,by linarith⟩ ⟨[0,1,2],by exact List.dedup_eq_self.mp rfl⟩
= { ⟨Sym2.mk (0,1),by simp⟩, ⟨Sym2.mk (1,2),by simp⟩} := by
  unfold Permut_to_Edgeset Permut_to_Edgeset Permut_to_Edgeset
  simp; grind

/- Turns CycleDef(Permutation) into CycleDef(Edgeset)
   Forces Pemutation to be longer than 3 -/
private def Permut_to_Cycset' ( S : Permutation n ) (h : S.1.length ≥ 3) : PEK n :=
  have t0 : S.1 ≠ [] := by by_contra cnt; rw [cnt] at h; contradiction
  have t1 : S.1.head t0 = S.1.getLast t0 ↔ ∃a, S.1 = [a] := by {
    constructor
    · intro a
      obtain ⟨S,pre⟩ := S
      unfold Permutation at pre
      simp only [Set.mem_setOf_eq] at pre; simp_all only
      induction' S with x xs IH
      · by_contra; contradiction
      · grind
    · intro a
      obtain ⟨x, a⟩ := a
      simp_all only [List.length_cons, List.length_nil, zero_add, ge_iff_le, Nat.not_ofNat_le_one]
  }
  have t2 : ∀ (x : Fin n.val), ¬S.1 = [x] := by {
    intro x; by_contra cnt; rw [cnt] at h; contradiction
  }
  have t3 : s(S.1.head t0, S.1.getLast t0) ∈ EK n := by {
    simp only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq]
    rw [t1]; simpa only [not_exists]
  }
/- The actual definition -/
{ ⟨Sym2.mk (S.1.head t0,S.1.getLast t0),t3⟩ } ∪ Permut_to_Edgeset n S
/- Turns CycleDef(Permutation) into CycleDef(Edgeset) and handles cases where l = 0,1 or 2 -/
def Permut_to_Cycset ( S : Permutation n ) : PEK n :=
  if h : S.1.length ≥ 3 then Permut_to_Cycset' n S h else ∅
/- Small sanity checks -/
private example :
Permut_to_Cycset ⟨5,by linarith⟩ ⟨[0,4,2],by exact List.dedup_eq_self.mp rfl⟩
= { ⟨Sym2.mk (0,4),by simp⟩, ⟨Sym2.mk (4,2),by simp⟩, ⟨Sym2.mk (0,2),by simp⟩} := by
  simp [Permut_to_Cycset, Permut_to_Cycset']
  unfold Permut_to_Edgeset Permut_to_Edgeset Permut_to_Edgeset
  grind
private example :
Permut_to_Cycset ⟨3,by linarith⟩ ⟨[0,2],by exact List.dedup_eq_self.mp rfl⟩ = ∅ := by
  simp [Permut_to_Cycset]

/- =============================================== -/

/- # Cycle Equivalence Class # -/
/- The euqivalence relation -/
abbrev CycEq (C1 C2 : Permutation n) := Permut_to_Cycset n C1 = Permut_to_Cycset n C2
/- The cycle type is a set of equivalence classes over permutations over Fin n
   An instance of an setoid(Equivalence class) is declared first... -/
instance PermutationSetoid : Setoid (Permutation n) where
  r := CycEq n
  iseqv := {
    refl := by intro; simp only [CycEq]
    symm := by intro S1 S2 h; simp_all only [CycEq]
    trans := by intro S1 S2 S3 h0 h1; simp_all only [CycEq]
  }
/- That setoid is turned into a type giving a equivalence class type -/
def UCycle := Quotient (PermutationSetoid n)
-- Properties
noncomputable instance : Fintype (UCycle n) := by
  unfold UCycle; exact Fintype.ofFinite (Quotient (PermutationSetoid n))

/- Some useful functions -/
/- This maps cycle equivalence classes to their respective edgeset -/
def UCycle_to_Cycset ( S : UCycle n ) : PEK n :=
  Quotient.lift
    (fun s ↦ Permut_to_Cycset n s)
    (by intro S1 S2 h; simp_all only; exact h)
    S
/- This maps cycle equivalence classes to their length -/
noncomputable def UCycle_len ( S : UCycle n ) : ℕ :=
  Quotient.lift
    (fun s ↦ (Permut_to_Cycset n s).ncard )
    (by intro S1 S2 h;simp_all only;rw[h])
    S

/- A subtype containing only cycles of a certain length -/
def UCycL := { (C : (UCycle n)) | UCycle_len n C = l.1}
-- Properties :
noncomputable instance : Fintype (UCycL n l) := by
  unfold UCycL; exact setFintype {C | UCycle_len n C = l.val}

/- =============================================== -/

/- # Theorems # -/

/- # ..Cycles # -/
/- #Cycles possible given a Graph of size n -/
noncomputable def UCycL.num := (UCycL n l).ncard

/- TODO: Prove that there are exactly n choose k cycles of length l in a graph of size n
   NOTE that l is forced to be ≥3 !! This might be extremely hard :( -/
theorem UCycL.num_val : UCycL.num n l = Nat.choose n.1 l.1 := by sorry

/- # ..Probability i.e. 𝔼/ℙ # -/
/- The expected number of cycles with length l-/
noncomputable def Ecyc_eqL := ∑(C : UCycL n l), Pr_EsubG p n (UCycle_to_Cycset n C)

/- TODO: Prove that 𝔼[#cycles with length l] = n choose k * p^l -/
theorem Ecyc_eqL_val : Ecyc_eqL n p l = Nat.choose n.1 l.1 * p.1^l.1 := by sorry
