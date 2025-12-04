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
  have h : ICard.toFinset.Nonempty := by { -- show ICard
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
