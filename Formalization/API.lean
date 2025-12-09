import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}
variable (n : ℕ){_ : n > 0}
variable (p : ℝ≥0)(le_one: p ≤ 1)

/- # 1 Basics # -/
/- We will sample from the complete Graph on n nodes-/
def Fingraph := SimpleGraph (Fin n)
def KGraph : Fingraph n := SimpleGraph.completeGraph (Fin n)

abbrev VK := Fin n -- Vertex Set
instance VK_nonempty (h : n > 0) : Nonempty (VK n) := by
  exact Fin.pos_iff_nonempty.mp h
abbrev PVK := Set (Fin n) -- Vertex Powerset
noncomputable instance : Fintype (PVK n) := by
  exact Fintype.ofFinite ↑(PVK n)
instance PVK_nonempty : Nonempty (PVK n) := by
  exact instNonemptyOfInhabited

/- Initialize the edgeset we will be using -/
abbrev EK := (KGraph n).edgeSet
noncomputable instance : Fintype (EK n) := by
  exact Fintype.ofFinite ↑(EK n)
abbrev PEK := Set (EK n)
noncomputable instance : Fintype (PEK n) := by
  exact Set.fintype

/- # Probability 1 # -/
/- Create our sample space ΩK which is a finite dependent type -/
abbrev ΩK := (KGraph n).edgeSet → Bool
noncomputable instance : Fintype (ΩK n) := by -- is finite type
  exact Pi.instFintype
instance : DiscreteMeasurableSpace (ΩK n) := by -- is DiscreteMeasurableSpace
  exact MeasurableSingletonClass.toDiscreteMeasurableSpace

/- Get a bernoulli measure ⇒
Create a bernoulli PMF, then convert that to a Measure -/
noncomputable def μ_bernoulli : Measure Bool :=
  (PMF.bernoulli p le_one).toMeasure
  deriving IsProbabilityMeasure
/- Defines a Measure over sample space ΩK by taking the product
   of the bernoulli measures over all edges.
   By hovering over #check, you see its type signature. -/
noncomputable abbrev EKμ : Measure (ΩK n) :=
  Measure.pi fun (_ : EK n) ↦ (μ_bernoulli p le_one)
noncomputable instance EKμIsProbMeas : IsProbabilityMeasure (EKμ n p le_one) := by
  exact Measure.pi.instIsProbabilityMeasure fun _ ↦ μ_bernoulli p le_one
#check EKμ
/- Define a PMF over ΩK
   This definition is equivalent to the powerset measurable space
   formalization approach, but easier to handle in Lean 4.
   Think of what each instance of Ω G (i.e. a concrete function) signifies. -/
noncomputable def EKpmf : PMF (ΩK n) :=
  (EKμ n p le_one).toPMF

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
noncomputable def αG (f : ΩK n)(pre : n > 0) : ℕ :=
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
      have : Nonempty (VK n) := VK_nonempty n pre
      exact Set.exists_mem_of_nonempty (VK n)
    }; have v : VK n := Classical.choose prop -- Choose a vertex | need to prove choose_spec?

    rw [@Set.nonempty_def];unfold IndSets; use {v}
    simp only
      [Subtype.forall, ne_eq,
      Subtype.mk.injEq, Set.mem_setOf_eq, Set.mem_singleton_iff,
      forall_eq, not_true_eq_false,
      SimpleGraph.irrefl, imp_self]
  }
  ICard.toFinset.max' h -- GET THE ACTUAL NUMBER

/- # 2.3 Chromatic Number χ(G) # -/
/- Get minimal coloring of graph i.e. χ(G) -/
-- TODO @LUCAS, try if you want :)
  -- Notice: VERY DOABLE, Just keep in mind that RGraph n f is a subgraph defined by f.


/- # 3. Probability-2 # -/
/- # Defs #-/


/- # 3.0 Base # -/
/- Probability of an edge existing is p
   Pr[e exists in G] = p -/
theorem ℙe (p : ℝ≥0)(le_one : p ≤ 1):
let meas := EKμ n p le_one;
∀(e : EK n), meas.real {f | f e} = p := by
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
  rw [show ((p : ℝ≥0∞) + (1 - p)) = 1 from by
    rw [add_tsub_cancel_of_le]; exact ENNReal.coe_le_one_iff.mpr le_one]
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
  conv =>
    enter [1,2]
    simp only [ENNReal.toReal_one, one_pow]
  norm_cast; norm_num

/- # 3.1 ℙ/𝔼 Cycles # -/
/- Probability of #cycles with length ≤ l = X -/
noncomputable def ℙcycle (l : ℕ)(X : ℕ) :=
  (EKμ n p le_one) (cycSet_le n l X)
/- Expected Value 𝔼[X] of #cycles with length ≤ l -/
noncomputable def 𝔼cycle (l : ℕ) :=
  ∑(i ∈ Finset.range n), i * (ℙcycle n p le_one l i)

/- # 3.2 ℙ Independent Sets / α(G) # -/
/- Probability of α(G) being bigger equal num -/
noncomputable def ℙαG_ge (num : ℕ)(pre : n > 0) : ℝ≥0∞ :=
  let meas := EKμ n p le_one;
  meas {f : (ΩK n) | αG n f pre ≥ num}
/- Some theorems about that -/
-- @Lucas maybe

/- # 3.3 𝔼 Cycles # -/
/- The expected number of cycles ≤ l -/
/- # 3.3.1 𝔼 Cycles Theorems # -/
/- Some theorems about that -/
-- @Lucas maybe
