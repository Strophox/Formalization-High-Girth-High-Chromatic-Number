import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}

/- # 1 Basics # -/
/- Our probability values -/
structure ℙval where
  val   : ℝ≥0
  proof : val ≤ 1
structure Nval where
  val   : ℕ
  proof : val > 0

section
variable (p : ℙval)
variable (n : Nval)

/- Graph types and Graph constants -/
abbrev Fingraph := SimpleGraph (Fin n.1) -- Our graph type
abbrev KGraph : Fingraph n := SimpleGraph.completeGraph (Fin n.1) -- A complete Graph

/- Vertex Set -/
abbrev VK := Fin n.1
-- Properties :
instance VK_nonempty : Nonempty (VK n) := by
  exact Fin.pos_iff_nonempty.mp n.2

/- Vertex Power Set -/
abbrev PVK := Set (Fin n.1)
noncomputable instance : Fintype (PVK n) := by
  exact Fintype.ofFinite ↑(PVK n)
-- Properties :
instance PVK_nonempty : Nonempty (PVK n) := by
  exact instNonemptyOfInhabited

/- Complete EdgeSet -/
abbrev EK := (KGraph n).edgeSet
-- Properties :
noncomputable instance : Fintype (EK n) := by
  exact Fintype.ofFinite ↑(EK n)

/- Complete EdgePowerSet -/
abbrev PEK := Set (EK n)
-- Properties :
noncomputable instance : Fintype (PEK n) := by
  exact Set.fintype

/- # Probability 1 # -/
/- Graph Sample Space ⇒
The universe of functions Edges -> Bool -/
abbrev ΩK := (EK n) → Bool
-- Properties :
noncomputable instance : Fintype (ΩK n) := by
  exact Pi.instFintype
instance : DiscreteMeasurableSpace (ΩK n) := by
  exact MeasurableSingletonClass.toDiscreteMeasurableSpace

/- Bernoulli Measure ⇒
Cast from a bernoulli PMF -/
noncomputable def μ_bernoulli : Measure Bool :=
  (PMF.bernoulli p.1 p.2).toMeasure
  deriving IsProbabilityMeasure
/- Defines a Measure over sample space ΩK by taking the product
   of the bernoulli measures over all edges.
   By hovering over #check, you see its type signature. -/
noncomputable abbrev EKμ : Measure (ΩK n) :=
  Measure.pi fun (_ : EK n) ↦ (μ_bernoulli p)
noncomputable instance EKμIsProbMeas : IsProbabilityMeasure (EKμ p n) := by
  exact Measure.pi.instIsProbabilityMeasure fun _ ↦ μ_bernoulli p
#check EKμ
/- Define a PMF over ΩK
   This definition is equivalent to the powerset measurable space
   formalization approach, but easier to handle in Lean 4.
   Think of what each instance of Ω G (i.e. a concrete function) signifies. -/
noncomputable def EKpmf : PMF (ΩK n) :=
  (EKμ p n).toPMF

/- # 1.1 Graphs # -/
/- Define a random subgraph sampled from KGraph n
   The random subgraph is sampled via a function f from our sample space -/
def RGraph (f : ΩK n) : Fingraph n where
  Adj u v :=
    (KGraph n).Adj u v ∧ ( (h : (KGraph n).Adj u v) → f ⟨ s(u, v),
      by rw [SimpleGraph.mem_edgeSet, KGraph]; simpa only [ne_eq] ⟩ )
  symm := by {
    rintro a b ⟨h1,h2⟩
    constructor
    · symm; assumption
    · intros adj
      specialize h2 h1
      conv =>
        enter [1,1,1]
        rw [Sym2.eq_swap]
      assumption
  }

noncomputable instance (f : ΩK n): let G := (RGraph n f); G.LocallyFinite := by {
  simp only
  intro v
  exact Fintype.ofFinite ↑(SimpleGraph.neighborSet (RGraph n f) v)
}


/- # 2 Properties # -/

/- # 2.1 Number of cycles of length ≤ l # -/
/- E is Cycleset containing cycles with length ≤ l -/
abbrev isCycleset (E : PEK n)(f : ΩK n)(l : ℕ) :=
  let G := RGraph n f;
  E.ncard ≤ l ∧ ∃(v : VK n)(p : G.Walk v v), p.IsCycle ∧ {e | e ∈ p.edges} = E
/- Helpers that might be useful later -/
noncomputable abbrev CycleSetCard (f : ΩK n)(l : ℕ) :=
  {Cyc | isCycleset n Cyc f l}.ncard
noncomputable abbrev CycleSetRed (f : ΩK n)(l : ℕ): PEK n :=
  ⋃₀{Cyc | isCycleset n Cyc f l}
/- The set of Graphs that contain exactly X cycles of length ≤ l -/
def cycSet_le (l : ℕ)(X : ℕ) : Set (ΩK n) :=
  {f | CycleSetCard n f l = X }

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

/- # 2.3 Chromatic Number χ(G) # -/
/- Get minimal coloring of graph i.e. χ(G) -/
-- TODO @LUCAS, try if you want :)
  -- Notice: VERY DOABLE, Just keep in mind that RGraph n f is a subgraph defined by f.


/- # 3. Probability-2 # -/
/- # Defs #-/


/- # 3.0 Base # -/
/- Probability of an edge existing is p
   Pr[e exists in G] = p -/
theorem ℙe : let meas := EKμ p n;
∀(e : EK n), meas.real {f | f e} = p.1 := by
  intro M e
  -- "Unfold" Measure Theory stuff
  rw [Measure.real_def]
  simp only [EKμ, μ_bernoulli, M]
  -- I dont get this
  let s : EK n → Set Bool := fun e' : EK n => if e' = e then {true} else Set.univ
  -- Proof that universe of above functions is equal to the event that edge e is in random graph
  -- I will try to understand it better. The have : ... below is mostly copied from prof
  have set_eq : { (f : ΩK n) | f e = true} = Set.univ.pi s := by {
    ext f
    constructor
    · intro h
      simp_all only [Set.mem_setOf_eq, Bool.univ_eq, Set.mem_pi, Set.mem_univ,
        forall_const, Subtype.forall, s]
      intro a b
      obtain ⟨val, property⟩ := e
      simp_all only [Subtype.mk.injEq]
      split
      next h_1 =>
        subst h_1
        simp_all only [Set.mem_singleton_iff]
      next h_1 => simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Bool.eq_false_or_eq_true_self]
    · intro h
      simp only [Set.mem_setOf_eq]
      have := h e (Set.mem_univ _)
      simpa [s]
  }
  -- Rewrite/Simping to get numbers so that we get to see a normal definition with NUMBERS!!
  rw [set_eq]; rw [@Measure.pi_pi]; rw [@Finset.prod_apply_ite]
  -- SIMP did something
  simp only [PMF.toMeasure_apply_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Set.mem_singleton_iff,
    Set.indicator_of_mem, PMF.bernoulli_apply, cond_true, Finset.sum_singleton, Bool.false_eq_true,
    Set.indicator_of_notMem, add_zero, Finset.prod_const, Bool.univ_eq, Set.mem_insert_iff,
    Bool.eq_false_or_eq_true_self, cond_false, ENNReal.coe_sub, ENNReal.coe_one, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  -- Solve Equations involving numbers to get the desired result.
  rw [show ((p.val : ℝ≥0∞) + (1 - p.val)) = 1 from by
    rw [add_tsub_cancel_of_le]
    exact ENNReal.coe_le_one_iff.mpr p.2]
  -- conv is ADVANCED REWRITING technique
  conv =>
    enter [1,1,2]
    rw [show ({x | x = e} : Finset _).card = 1 from by
      rw [@Finset.card_eq_one]; use e
      -- AESOP did something
      simp_all only [Bool.univ_eq, s]
      obtain ⟨val, property⟩ := e
      ext a : 1
      simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]]
      -- AESOP won
  conv =>
    enter [1,2]
    simp only [ENNReal.toReal_one, one_pow]
  norm_cast; norm_num

/- # 3.1 ℙ/𝔼 Cycles # -/
/- Probability of #cycles with length ≤ l = X -/
noncomputable def ℙcycle (l : ℕ)(X : ℕ) :=
  (EKμ p n) (cycSet_le n l X)
/- Expected Value 𝔼[X] of #cycles with length ≤ l -/
noncomputable def 𝔼cycle (l : ℕ) :=
  ∑(i ∈ Finset.range n.1), i * (ℙcycle p n l i)

/- # 3.2 ℙ Independent Sets / α(G) # -/
/- Probability of α(G) being bigger equal num -/
noncomputable def ℙαG_ge (num : ℕ)(pre : n > 0) : ℝ≥0∞ :=
  let meas := EKμ n p le_one;
  meas {f : (ΩK n) | αG n f pre ≥ num}
/- Some theorems about that -/
-- @Lucas maybe
end
