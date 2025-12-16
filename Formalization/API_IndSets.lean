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

/- # Defs  # -/
/- Constructs a complete subgraph given a set of Vertices -/
def CompleteEdgeSubset (I : PVK n) : PEK n:=
  let : Fintype I := by exact Fintype.ofFinite ↑I;
  let I2 := I.toFinset.powersetCard 2;
  let : Fintype I2 := by exact I2.fintypeCoeSort;
  have : ∀i2, i2 ∈ I.toFinset.powersetCard 2 → List.Nodup i2.toList := by {
    intros pair i; exact Finset.nodup_toList pair }
  I2.attach.image (
   fun ⟨S,h_mem⟩ ↦
   match h : S.toList with
    | a::b::[] => ( ⟨ s(↑a,↑b),by -- The actual mapping
      have : List.Nodup S.toList := by {exact Finset.nodup_toList S}
      simp_all only [Finset.mem_powersetCard,
        Set.subset_toFinset, and_imp, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_false_eq_true, List.nodup_nil, and_self, and_true, SimpleGraph.edgeSet_top,
        Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq] ⟩
      : (EK n) )
    -- Everything below here is just to say that these cases are impossible
    | [] => by exfalso;subst I2;simp_all only [Finset.mem_powersetCard, Set.subset_toFinset,
      and_imp, Finset.toList_eq_nil, Finset.coe_empty, Set.empty_subset, Finset.card_empty,
      OfNat.zero_ne_ofNat, and_false]
    | [a] => by exfalso;subst I2;simp_all only [Finset.mem_powersetCard, Set.subset_toFinset,
      and_imp, Finset.toList_eq_singleton_iff, Finset.coe_singleton, Set.singleton_subset_iff,
      Finset.card_singleton, OfNat.one_ne_ofNat, and_false]
    | a::b::c::S => by
      exfalso;subst I2;expose_names
      have : S_1.toList.length = (S_1).card := by exact Finset.length_toList S_1
      simp_all only [Finset.mem_powersetCard, Set.subset_toFinset, and_imp, List.length_cons,
        Nat.reduceEqDiff]
  )


end API_𝕀
