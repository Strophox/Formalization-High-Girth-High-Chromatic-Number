
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.commandStart false

/- # 2.2 Maximal Independent Set α(G) # -/

/- complement of graph sample -/
abbrev f_complement (f : ΩK n) : ΩK n := fun e ↦ !(f e)
/- checks if a given subset of vertices is fully connected -/
abbrev isK (G : Fingraph n)(I : PVK n) :=
  ∀(u v : I), u ≠ v → G.Adj u v

/- Get α(G)
NOTE : Changed to circumvent difficult classical.choose existence proof
NOTE : Lost access to explicit max independent set -/
noncomputable def αG (f : ΩK n) : ℕ :=
  let G := RGraph n (f_complement n f);
  let IndSets := { I : PVK n | isK n G I };
  let f (I : PVK n) : ℕ := I.ncard; -- function mapping the independent sets to their cardinalities
  let ICard : Set ℕ := f '' IndSets; -- set containing all the cardinalities
  let : Fintype ICard := by exact Fintype.ofFinite ↑ICard -- Tell Lean ICard can be a finite type

  have h : ICard.toFinset.Nonempty := by { -- show that ICard nonempty

    refine Set.Aesop.toFinset_nonempty_of_nonempty ?_
    have h : IndSets.Nonempty → ICard.Nonempty := by
      exact fun a ↦ Set.Nonempty.image f a
    apply h; clear h

    let prop : ∃v, v ∈ (Set.univ : Set (VK n)) := by {
      have : Nonempty (VK n) := VK_nonempty n
      exact Set.exists_mem_of_nonempty (VK n)
    }; have v : VK n := Classical.choose prop
    -- chosen a vertex | need to prove choose_spec?

    rw [@Set.nonempty_def]; unfold IndSets; use {v}
    simp only
      [Subtype.forall, ne_eq,
      Subtype.mk.injEq, Set.mem_setOf_eq, Set.mem_singleton_iff,
      forall_eq, not_true_eq_false,
      SimpleGraph.irrefl, imp_self]
  }

  ICard.toFinset.max' h -- get number
