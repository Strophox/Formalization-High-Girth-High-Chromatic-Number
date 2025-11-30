import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.style.commandStart false

variable {α : Type*}
variable {n : ℕ}
variable (p : ℝ≥0)(le_one: p ≤ 1)

def FinGraph (n : ℕ) := SimpleGraph (Fin n)
variable {G : FinGraph n}
abbrev E (G : FinGraph n) := G.edgeSet

/- # Probability Notions # -/
/- A dependent type ( Ω ) which will act as our sample space.
   Our sample space will the the set of all functions
   mapping from Edges to Bool. -/
abbrev Ω (G : FinGraph n) := (E G) → Bool

-- Show that (E G) and Ω are Finite Types
noncomputable instance : Fintype (E G) := by
  exact Fintype.ofFinite (E G)
noncomputable instance : Fintype (Ω G) := by
  exact Fintype.ofFinite (Ω G)
-- Show that Ω is a Discrete Measurable Space
/- This works because
   Ω is an instance of a Pi type, i.e. dependent type, and
   Pi.instMeasurableSingletonClass is given by Lean.
   Note that Bool is a Measurable Space. -/
instance : DiscreteMeasurableSpace (Ω G) := by
  exact MeasurableSingletonClass.toDiscreteMeasurableSpace

-- Convert PMF into a Measure in preparation for 'Measure.pi'
noncomputable def bernoulli_bool : Measure Bool :=
  (PMF.bernoulli p le_one).toMeasure
  deriving IsProbabilityMeasure
/- Defines a Measure over sample space Ω G by taking the product
   of the bernoulli measures over all edges. (Ask Fadri for theoretical details)
   By hovering over #check E_measure, you can check its type signature. -/
noncomputable abbrev E_measure (G : FinGraph n) :=
  Measure.pi fun _ : E G ↦ (bernoulli_bool p le_one)
#check E_measure
noncomputable instance : IsProbabilityMeasure (E_measure p le_one G) := by
  refine Measure.pi.instIsProbabilityMeasure fun x ↦ bernoulli_bool p le_one

-- Reconvert into a PMF again.
/- This definition is equivalent to the powerset measurable space
   formalization approach, but easier to handle in Lean 4.
   Think of what each instance of Ω G (i.e. a concrete function) signifies. -/
noncomputable def Eset_PMF : PMF (Ω G) := (E_measure p le_one G).toPMF

/- # General Definition of Graphs # -/
-- Complete Graph
def KGraph : FinGraph n where
  Adj u v := u ≠ v
-- This samples a subgraph according to a function f from our sample space
def RSubGraph (f : Ω G) : FinGraph n where
  Adj u v :=
    G.Adj u v ∧ ((h:G.Adj u v) → f ⟨s(u, v), by rwa [SimpleGraph.mem_edgeSet]⟩)
  symm := by {
    rintro a b ⟨h1,h2⟩
    constructor
    · rw [←SimpleGraph.mem_edgeSet] at *
      rwa [Sym2.eq_swap]
    · intros adj
      specialize h2 h1
      conv =>
        enter [1,1,1]
        rw [Sym2.eq_swap]
      assumption
  }
