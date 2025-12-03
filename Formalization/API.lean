import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}
variable (n : ℕ)
variable (p : ℝ≥0)(le_one: p ≤ 1)

/- # 1 Basics # -/
/- We will sample from the complete Graph on n nodes-/
def Fingraph := SimpleGraph (Fin n)
def KGraph : Fingraph n := SimpleGraph.completeGraph (Fin n)

abbrev VK := Fin n -- Vertex Set
abbrev PVK := Set (Fin n) -- Vertex Powerset
noncomputable instance : Fintype (PVK n) := by
  exact Fintype.ofFinite ↑(PVK n)

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

/- Get maximal independent set -/
noncomputable def maxIndSet (f : ΩK n) : PVK n :=
  let G := RGraph n (f_complement n f); -- take complement of graph so we can use cliques
  let maxIndSet : -- For classical.choose
    ∃(Imax : PVK n),isK n G Imax ∧ ∀(I: PVK n), isK n G I → Imax.ncard ≥ I.ncard :=
    by sorry
    -- PROOF that a maximal Independent set always exists
    -- Somehow show that existence of a independent set → existence of maximal set
    -- Seems very hard, but we need!
  Classical.choose maxIndSet

/- Get α(G) -/
noncomputable def αG (f : ΩK n) : ℕ :=
  (maxIndSet n f).ncard


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
/- Some theorems about that -/
-- @Lucas maybe

/- # 3.2 ℙ Independent Sets / α(G) # -/
/- Probability of α(G) being bigger equal num -/
noncomputable def ℙαG_ge (num : ℕ) : ℝ≥0∞ :=
  let meas := EKμ n p le_one;
  meas {f : (ΩK n) | αG n f ≥ num}
/- Some theorems about that -/
-- @Lucas maybe

/- # 3.3 𝔼 Cycles # -/
/- The expected number of cycles ≤ l -/
noncomputable def 𝔼cyc_l (l : ℕ): ℝ≥0∞ :=
  ∑(f : ΩK n), (num_cyc_le n f l) * ((EKpmf n p le_one) f)
/- Some theorems about that -/
-- @Lucas maybe
