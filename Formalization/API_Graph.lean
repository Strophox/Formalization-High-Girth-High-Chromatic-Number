import Mathlib

set_option autoImplicit false
set_option linter.style.commandStart false
variable {α : Type*}

namespace API_𝔾

structure Nval where
  val   : ℕ
  proof : val > 0
variable (n : Nval)

/- =============================================== -/
/- # DEFS # -/
/- =============================================== -/

/- =============================================== -/
/- Graph types and Graph constants -/
abbrev Fingraph := SimpleGraph (Fin n.1) -- Our graph type
abbrev KGraph : Fingraph n := SimpleGraph.completeGraph (Fin n.1) -- A complete Graph
/- =============================================== -/

/- =============================================== -/
/- Vertex Set -/
abbrev VK := Fin n.1
-- PROPERTIES
instance : Fintype (VK n) := by
  exact Fin.fintype n.val
instance : DecidableEq (VK n) := by
  exact instDecidableEqFin n.val
instance VK_nonempty : Nonempty (VK n) := by
  exact Fin.pos_iff_nonempty.mp n.2
/- =============================================== -/

/- =============================================== -/
/- Vertex Power Set -/
abbrev PVK := Set (Fin n.1)
-- PROPERTIES
noncomputable
instance : Fintype (PVK n) := by
  exact Fintype.ofFinite ↑(PVK n)
noncomputable
instance (I : PVK n) : Fintype I := by
  exact Fintype.ofFinite ↑I
instance : Nonempty (PVK n) := by
  exact instNonemptyOfInhabited
/- =============================================== -/

/- =============================================== -/
/- Complete EdgeSet -/
abbrev EK := (KGraph n).edgeSet
-- Properties :
noncomputable instance : Fintype (EK n) := by
  exact Fintype.ofFinite ↑(EK n)
noncomputable instance : DecidableEq (EK n) := by
  exact instDecidableEqOfLawfulBEq
-- Helpers
@[scoped simp 10]
theorem mem_EK_iff : ∀(n : Nval),∀(a b), s(a, b) ∈ EK n ↔ a ≠ b := by {
  intros n a b;
  simp only [SimpleGraph.edgeSet_top, Set.mem_setOf_eq, Sym2.isDiag_iff_proj_eq, ne_eq]
}
/- =============================================== -/

/- =============================================== -/
/- Complete EdgePowerSet -/
abbrev PEK := Set (EK n)
-- Properties :
noncomputable instance : Fintype (PEK n) := by
  exact Set.fintype
noncomputable instance : DecidableEq (PEK n) := by
  exact Classical.typeDecidableEq (PEK n)
/- =============================================== -/

/- =============================================== -/
/- Sets of Edgesets -/
abbrev PPEK := Set (PEK n)
-- Properties :
noncomputable instance : Fintype (PPEK n) := by
  exact Set.fintype
noncomputable instance (E': PPEK n): Fintype E' := by
  exact Fintype.ofFinite ↑E'
noncomputable instance PPEK_Countable (E': PPEK n) : Set.Countable E' := by
  exact Set.to_countable E'
/- =============================================== -/

/- =============================================== -/
/- # PROOFS ABOUT GRAPH PROPERTIES #
   Given n cycles there exists a choice of at most n vertices that destroys these cycles
    -- Show that removing a vertex from a cycle destroys it [TODO]
    -- Show that overlapping vertices only decrease the amount of vertices needed. [TODO]

   αG' ≤ αG for any G induced Graph G' [TODO]
    -- Show that for any Graph removing a vertex never increases α [TODO]
    -- induction to say this is true for any number of removals [TODO]

   χ(G) * α(G) ≥ |G| [TODO]
    -- Show that every set of same colored vertices is a independent set [TODO]
    -- Show that ∑(c : Color) |Iᶜ| = |G| [TODO]
    -- Show that ∀(c : Color) |Iᶜ| ≤ α(G). [TODO]
    -- Derive inequality [TODO]
   -/
/- =============================================== -/

end API_𝔾
