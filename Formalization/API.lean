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
   of the bernoulli measures over all edges. (Ask Fadri for theoretical details)
   By hovering over #check, you see its type signature. -/
noncomputable abbrev EKμ :=
  Measure.pi fun (_ : EK n) ↦ (μ_bernoulli p le_one)
noncomputable instance : IsProbabilityMeasure (EKμ n p le_one) := by -- is ProbabilityMeasure
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

/- # 2 Properties # -/
/- # 2.1 Number of cycles of length ≤ l # -/
/- Get number of cycles with exactly length l in G
   @LUCAS, can you try finding out wtΣ a SIGMA type is????
   @LUCAS, check correctness
   @LUCAS, check if we need this to be computable -/
noncomputable def num_cyc_eq (G : Fingraph n)(l : ℕ) : ℕ :=
  if l ≤ 2 then 0 else -- No cycles with length ≤ 2
    let cycles_l : Set (Σ (v : Fin n), G.Walk v v) := -- This here is a sigma type
      { p | p.2.IsCycle ∧ p.2.length = l};
  (cycles_l.ncard) / l
/- Get number of cycles less or equal than l-/
noncomputable def num_cyc_le (f : ΩK n)(l : ℕ) : ℕ :=
  let G := RGraph n f;
  ∑(i ∈ Finset.range l), num_cyc_eq n G i


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
/- Probability of a set of edges E existing is p^|E|
   Pr[E is contained in G] = p^|E| -/
abbrev E_isContained (E : Set (EK n))(f : ΩK n) := ∀(e : E), f e
theorem ℙE (p : ℝ≥0)(le_one : p ≤ 1):
let meas := EKμ n p le_one;
∀(E : Set (EK n)), meas.real {f | E_isContained n E f} = p^(E.ncard) := by
  intro M E
  rw [Measure.real_def]
  simp only [EKμ, μ_bernoulli, M]

  let (e : EK n): Decidable (e ∈ E) := by exact Classical.propDecidable (e ∈ E)
  let s : EK n → Set Bool := fun e' : EK n => if e' ∈ E then {true} else Set.univ

  have set_eq : {f | E_isContained n E f} = Set.univ.pi s := by {
    ext f
    constructor
    · -- AESOP did a thing
      intro a
      simp_all only [Subtype.forall, Set.mem_setOf_eq,
        Bool.univ_eq, Set.mem_pi, Set.mem_univ, forall_const, s]
      intro a_1 b
      split
      next h => simp_all only [Set.mem_singleton_iff]
      next h => simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Bool.eq_false_or_eq_true_self]
    · intro h
      simp only [Set.mem_setOf_eq, E_isContained]
      intro e
      have := h e (Set.mem_univ _)
      simpa [s]
  }

  rw [set_eq]; rw [@Measure.pi_pi]; rw [@Finset.prod_apply_ite]
  simp only [PMF.toMeasure_apply_fintype, Fintype.univ_bool, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Set.mem_singleton_iff,
    Set.indicator_of_mem, PMF.bernoulli_apply, cond_true, Finset.sum_singleton, Bool.false_eq_true,
    Set.indicator_of_notMem, add_zero, Finset.prod_const, Bool.univ_eq, Set.mem_insert_iff,
    Bool.eq_false_or_eq_true_self, cond_false, ENNReal.coe_sub, ENNReal.coe_one, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  rw [show ((p : ℝ≥0∞) + (1 - p)) = 1 from by
    rw [add_tsub_cancel_of_le]; exact ENNReal.coe_le_one_iff.mpr le_one]
  conv =>
    enter [1,2]
    simp only [ENNReal.toReal_one, one_pow]
  norm_cast; norm_num
  conv =>
    enter [1, 2, 1]
    rw [show ({x | x ∈ E} : Finset (EK n)) = E.toFinset from by
      exact Set.filter_mem_univ_eq_toFinset E]
  congr
  exact Eq.symm (Set.ncard_eq_toFinset_card' E)

/- # 3.1 ℙ Cycles # -/
/- Probability of number of cycles ≤ l being bigger equal num -/
noncomputable def ℙcyc_l_ge (num : ℕ)(l : ℕ) : ℝ≥0∞ :=
  let meas := EKμ n p le_one;
  meas {f : (ΩK n) | num_cyc_le n f l ≥ num}
/- # 3.1.1 ℙ Cycles Theorems # -/
/- Some theorems about that -/
-- @Lucas maybe

/- # 3.2 ℙ Independent Sets / α(G) # -/
/- Probability of α(G) being bigger equal num -/
noncomputable def ℙαG_ge (num : ℕ)(pre : n > 0) : ℝ≥0∞ :=
  let meas := EKμ n p le_one;
  meas {f : (ΩK n) | αG n f pre ≥ num}
/- Some theorems about that -/
-- @Lucas maybe

/- # 3.3 𝔼 Cycles # -/
/- The expected number of cycles ≤ l -/
noncomputable def 𝔼cyc (l : ℕ) : ℝ≥0∞ :=
  ∑(f : ΩK n), (num_cyc_le n f l) * ((EKpmf n p le_one) f)
/- # 3.3.1 𝔼 Cycles Theorems # -/
theorem 𝔼cyc_val (l : ℕ) :
  𝔼cyc n p le_one l = ∑(i ∈ Finset.range l),(p^i * ∏(j ∈ Finset.range i),(n-j+1) / (2 * i)) := by
  sorry
/- Some theorems about that -/
-- @Lucas maybe
