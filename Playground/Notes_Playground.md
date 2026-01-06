# Project Proposal (Markdown transliteration)

## Overview

As a [Lean 4](https://lean-lang.org/) project for the ETHZ course [Formalizing Analysis of Algorithms (HS25)](https://www.vvz.ethz.ch/Vorlesungsverzeichnis/lerneinheit.view?semkez=2025W&ansicht=ALLE&lerneinheitId=196938&lang=en), we are to formalize an algorithm, or (extremal combinatorics) concept of our choice.

We propose to attempt formalizing a proof of the following theorem, which concerns the existence of (simple) graphs with high girth[^1] and high chromatic number[^2]:

[^1]: For a graph G, the girth γ(G) is the length of the smallest cycle.
[^2]: For a graph G, the chromatic number χ(G) is the number of colors needed to color the nodes such that no two adjacent nodes share the same color.

> Theorem (Erdős 1959)
> For any k, l ∈ N, there exists a graph G with γ(G) > l and χ(G) > k.

Such a formalization would follow a variation of Erdős’ original proof (Erdös 1959), akin to how it is commonly found in modern literature (Aigner and Ziegler 1999; Jukna 2011; Zhao 2019; Alon and Spencer 2016; Matoušek and Vondrák 2001).

The proof is often taken as an important example to demonstrate the [probabilistic method](https://en.wikipedia.org/wiki/Probabilistic_method) (and method of alterations) and touches on the general topics of [graph theory](https://en.wikipedia.org/wiki/Graph_theory), [probability theory](https://en.wikipedia.org/wiki/Probability_theory) and some [(asymptotic) analysis](https://en.wikipedia.org/wiki/Asymptotic_analysis).


## Planning

From analyzing the proof from various sources in literature, we are able to propose a more detailed outline for this project. Specifically, we list various concepts or hurdles that will likely be faced during formalization, including an informal estimate of the relative effort they might take us at this stage. Note that the listed efforts are biased to start at ‘noteworthy difficulty’, as those will be the most interesting but also increasingly tricky parts of our formalization.

Notation: (†) ≃ “likely of noteworthy difficulty”, (‡) ≃ “possibly of key difficulty”.

#### Varia

* Effective splitting into subproofs and formulation of lemmas.
* Many algebraic transformations of moderate difficulty (sums, inequalities).
* Asymptotic analyses. (†)

#### Probability theory

* Probability theory in Lean 4 using measure-based definitions (expected value, Markov inequality, random variables, etc.) (†)
* Defining and using [random graphs](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93R%C3%A9nyi_model) à la Erdős–Rényi. (†)
* Application of the probabilistic method. (‡)

#### Graph structures and -properties

* Counting the number of cycles in a graph of some length. (‡)
* [Girth](https://en.wikipedia.org/wiki/Girth_(graph_theory)) of a graph (γ(G)). (†)
* [Chromatic number](https://en.wikipedia.org/wiki/Graph_coloring) of a graph (χ(G)). (†)
* Size of the largest [independent set](https://en.wikipedia.org/wiki/Independent_set_(graph_theory)) of a graph (α(G)). (‡)
* Proving properties of induced subgraphs. (‡)


### On Using Mathlib

For probability, most libraries appear to be geared towards continuous probability distributions, in contrast to discrete ones, which is what is needed here. We thus decide to build the needed probability theory from scratch using the Mathlib [Measure Theory library](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html) and combining them (from scratch) with the graph concepts mentioned above.

Mathlib4 ostensibly supports [simple graphs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Basic.html), [graph coloring](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Coloring.html), [graph girth](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Girth.html), and [subgraphs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Subgraph.html), which we will try to make use of. There appears to be no support for independent sets, which we will have to formalize from scratch.

[Limits](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html#Filter.Tendsto) seem to be supported by Mathlib and we will make use of such.


## References

- Aigner, Martin and Günter M Ziegler (1999). “Proofs from the Book”. In: Berlin. Germany 1.2, p. 7.
- Alon, Noga and Joel H Spencer (2016). The probabilistic method. John Wiley & Sons.
- Erdös, Paul (1959). “Graph theory and probability”. In: Canadian Journal of Mathematics 11, pp. 34–38.
- Jukna, Stasys (2011). Extremal combinatorics: with applications in computer science. Vol. 571. Springer.
- Matoušek, Jiří and Jan Vondrák (2001). “The probabilistic method”. In: Lecture Notes, Department of Applied Mathematics, Charles University, Prague.
- Zhao, Yufei (2019). “18.218 Probabilistic Method in Combinatorics, Spring 2019”. In.


# Initial Main Proof Outline

```lean
theorem high_girth_high_chromatic_number {k : ℕ} {l : ℕ} : 2+2=4 := by

  --## let n := SPECIFIED LATER ℕ
  --#  let θ < 1 / l
  --#  let p := n^(θ - 1)
  --## let G ~ G(n, p)

  --## let X := "number of cycles in G of size ≤ l"

  --## E[X] = ∑ᵢ₌₃ˡ p^i         * ( n * (n-1) * ⋯ * (n-(i-1)) )/( 2*i )  by:facts and logic
  --#  E[X] ≤ ∑ᵢ₌₃ˡ n^(θ*i - i) * n^i                                    by:round up
  --#  E[X] ≤ ∑ᵢ₌₃ˡ n^(θ*i)                                              by:cancel
  --#  E[X] ≤ ∑ᵢ₌₃ˡ n^(θ*l)                                              by:round up
  --#  E[X] ≤ l * n^(θ*l)                                                by:sum of constants
  --#  P[X ≥ n/2] ≤ E[X] / (n/2)                                         by:Markov Inequality
  --#  P[X ≥ n/2] ≤ l * n^(θ*l) / (n/2)                                  by:grw E[X] ≤ l * n^(θ*l)
  --#  P[X ≥ n/2] ≤ 2 * l * n^(θ*l - 1)                                  by:reorder
  --#  P[X ≥ n/2] ≤ 2 * l * n^(-constant)                                by:recall θ<1/l ⇒ θ*l < 1
  --## lim n → ∞: P[X ≥ n/2] → 0                                         by: ???
  --#  ∀ ε>0, ∃ n₁, P[X ≥ n₁/2] < ε                                      by:def lim?

  --## let α(G) := "largest independent set of G"

  --#  let x := ⌈3/p * ln(n)⌉
  --## Pr[α(G) ≥ x] ≤ choose(n,x)                * (1 - p)^choose(x,2)       by:that's just how it is
  --#  Pr[α(G) ≥ x] ≤ ( n * ⋯ * n-(x-1) )/( x! ) * (1 - p)^(x*(x-1)/2)       by:def choose
  --#  Pr[α(G) ≥ x] ≤ ( n * ⋯ * n-(x-1) )/( x! ) *  e^(-p)^(x*(x-1)/2)       by:recall e^x := 1 + x + x^2/4 + …
  --#  Pr[α(G) ≥ x] ≤ ( n^x             )/( x! ) *  e^(-p)^(x*(x-1)/2)       by:round
  --#  Pr[α(G) ≥ x] ≤ ( e^(ln(n) * x)   )/( x! ) *  e^(-p)^(x*(x-1)/2)       by:n = e^ln(n)
  --#  Pr[α(G) ≥ x] ≤ ( e^(ln(n) * x)   )/( x! ) *  e^(-p/2 * (x-1) * x)     by:reorder
  --#  Pr[α(G) ≥ x] ≤ e^( ln(n) * x + -p/2 * (x-1) * x )/( x! )              by:reorder
  --#  Pr[α(G) ≥ x] ≤ e^( ln(n) - p/2 * (x-1)      )^x / ( x! )              by:reorder
  --#  Pr[α(G) ≥ x] ≤ e^( ln(n) - p/2 * (⌈3/p * ln(n)⌉-1)      )^x / ( x! )  by:rw x
  --## Pr[α(G) ≥ x] ≤ e^0  / ( x! )                                          by:okay this step sucks, something about ⌈3/p * ln(n)⌉ > 2/p * ln(n) + 1
  --## lim n → ∞: Pr[α(G) ≥ x] → 0                                           by: ???
  --#  ∀ ε>0, ∃ n₂, P[X ≥ n₂/2] < ε                                          by:def lim?

  --#  choose n = max(n₁, n₂), ε = 0.5  ⇝  G with P[X ≥ n₁/2] + P[X ≥ n₂/2] < 0.5 + 0.5    by:apply previous two stmts
  --## let G' := "G but with n/2 nodes removed  ⇝  there are no more small cycles"
  --## "G' has girth greater than l"                                                       by:facts and logic

  --## α(G') ≤ α(G)                            by:facts and logic
  --#  α(G') < x                               by:choice of n
  --#  α(G') < ⌈3/p * ln(n)⌉                   by:rw x

  --## χ(G') * α(G') ≥ |G'|                    by:facts and logic
  --#  χ(G') ≥ |G'| / α(G')                    by:reorder
  --#  χ(G') ≥ (n/2) / α(G')                   by:def G'
  --#  χ(G') ≥ (n/2) / ⌈3/p * ln(n)⌉           by:grw α(G') < ⌈3/p * ln(n)⌉
  --#  χ(G') ≥ (n/2) / ⌈3/n^(θ - 1) * ln(n)⌉   by:rw p
  --## lim n → ∞: χ(G') → ∞                    by: ??? this step REALLY sucks, we might have to choose a different 'x' to begin with
  --#  ∀ m, ∃ nₓ, χ(G') > m                    by:def lim?

  --#  adjust n = max(n, nₓ)  ⇝  χ(G') > k     by:apply previous stmt
  --# Qed.

  sorry
```


# Figuring out where to start with informal pattern matching

Given this vague correspondence:

```lean
-- Markov inequality "pleb version".
P[f ≥ ε] ≤ E[f] / ε
```

```lean
-- Markov inequality in Mathlib4.
theorem MeasureTheory.meas_ge_le_lintegral_div
   {α : Type u_1} -- Probability space/outcomes.
   [MeasurableSpace α]
   {μ : Measure α} -- Probability measure.
   {f : α → ENNReal} -- Random var.
  (hf : AEMeasurable f μ)
   {ε : ENNReal} -- Real numba or whatever.
  (hε : ε ≠ 0)
  (hε' : ε ≠ ⊤) :
    μ {x : α | f x ≥ ε } ≤ (∫⁻ (a : α), f a ∂μ) / ε
```
(<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.html#MeasureTheory.meas_ge_le_lintegral_div>)

We can "plug in" the values for the one place where we intend to use the Markov inequality in our proof:
```lean
P[X ≥ n/2] ≤ E[X] / (n/2)  -- X number of small cycles.
```

```lean
theorem MeasureTheory.meas_ge_le_lintegral_div
  {G(n,p) : Type u_1}  -- G(n,p) graphs type ?
  [MeasurableSpace G(n,p)]
  {# : Measure G(n,p)}  -- "#" Measure = count/number of elements(=graphs) divided by total elements(=graps) ?
  {X : G(n,p) → ENNReal}
  (hf : AEMeasurable X #)
  {"n/2" : ENNReal}
  (hε : n/2 ≠ 0)
  (hε' : n/2 ≠ ⊤) :
    # {g : G(n,p) | X g ≥ n/2 } ≤ (∫⁻ (g : G(n,p)), X g ∂#) / (n/2)
```

So we specifically see that we need:
* `G(n,p)` to be a `MeasureableSpace`,
* a counting measure(?) `# : Measure G(n,p)`,
* that `AEMeasurable X #`.


# Probability Structure Stuff

```lean
/- # General Probability Structure #
This structure is for defining general probability structures
over a n-size event space -/
structure Probability (α : Type*) where
 EventSpace     : MeasurableSpace α
 Measure        : PMF α

/-==============================================================-/
/-EXAMPLE COIN-/
noncomputable
def coin : Probability Bool where
 EventSpace := MeasurableSpace.generateFrom {{true},{false}}
 Measure := PMF.bernoulli (1/2 : ℝ≥0) (by norm_num)
/-FIRST PROOF YIPPIE!!!!!-/
example:
    coin.Measure false + coin.Measure true = 1 := by
    unfold coin; simp; rw[ENNReal.inv_two_add_inv_two]
/-==============================================================-/
```

```lean

Discarded Ideas are here

-- # DEFINING 'EDGES' #
-- 'Edges' is the underlying measure of our random Graph formalization and is foundational.
-- -/
-- abbrev Edges := G.edgeSet → Bool -- Determines if edge is in Graph
-- -- No clue what these do yet
-- noncomputable instance : Fintype (Edges G) := by exact Fintype.ofFinite (Edges G)
-- noncomputable instance {u v} :  Decidable (G.Adj u v) := by
--     exact Classical.propDecidable (G.Adj u v)
-- instance : DiscreteMeasurableSpace (Edges G) := by
--     exact MeasurableSingletonClass.toDiscreteMeasurableSpace

-- -- Our measure that maps an edge to its probability of existing
-- noncomputable
-- def unif_edge_measure (p : ℝ≥0)(h : p ≤ 1) : Measure Bool := (PMF.bernoulli p h).toMeasure
-- -- Proof that unif_edge_measure is indeed a probability measure
-- instance unif_edge_measure_isProbabilityMeasure {p : ℝ≥0}{h: p ≤ 1}:
--     IsProbabilityMeasure (unif_edge_measure p h):= by {
--         rw [@isProbabilityMeasure_iff]
--         simp only [Bool.univ_eq]
--         unfold unif_edge_measure
--         -- Bruhmetheus Momentum
--         simp only [PMF.toMeasure_apply_fintype, Fintype.univ_bool,
--           Set.mem_insert_iff, Set.mem_singleton_iff, Bool.eq_false_or_eq_true_self,
--           Set.indicator_of_mem, PMF.bernoulli_apply, Finset.mem_singleton, Bool.true_eq_false,
--           not_false_eq_true, Finset.sum_insert, cond_true, Finset.sum_singleton, cond_false,
--           ENNReal.coe_sub, ENNReal.coe_one]
--         simp_all only [ENNReal.coe_le_one_iff, add_tsub_cancel_of_le]
--     }
-- -- Maps an Edgeset to unif_edge_measure
-- instance unif_edgeset_measure_isProbabilityMeasure (p : ℝ≥0)(h:p ≤ 1) :
--     IsProbabilityMeasure (Measure.pi (fun _ : G.edgeSet ↦ unif_edge_measure p h)) :=
--     Measure.pi.instIsProbabilityMeasure fun _ ↦ unif_edge_measure p h
-- -- I think this tell Lean that this is a probability measure i.e. PMF. No clue exactly though
-- noncomputable
-- def Prob (p : ℝ≥0)(h: p ≤ 1) : PMF (Edges G) :=
--     (Measure.pi (fun _ => unif_edge_measure p h)).toPMF

-- /-
-- # Random Graphs Basic #
-- ATTENTION! Is only correct if ω is correctly formalized!
-- -/
-- noncomputable
-- def R_Graph (ω : Edges G) : SimpleGraph (Fin n) where
--     Adj u v := ∃(h : s(u,v) ∈ G.edgeSet), ω ⟨s(u,v),h⟩
--     loopless := by simp only [Irreflexive,
--         SimpleGraph.mem_edgeSet, SimpleGraph.irrefl,
--         IsEmpty.exists_iff, not_false_eq_true, implies_true]
--     symm := by
--         rintro u v ⟨h1,h2⟩
--         observe h : s(v,u) = s(u,v)
--         rw [h]; use h1

-- /-  Show that the probability function works correctly,
--     I.E. Edge should exist with probability p! -/
-- theorem Pr_edge {n : ℕ} (p : ℝ≥0) (h : p ≤ 1)
--   (G : SimpleGraph (Fin n)) :
--   let P := (Prob G p h).toMeasure;
--   ∀(e : Sym2 (Fin n))(h : e ∈ G.edgeSet), P.real {ω | ω ⟨e, h⟩ = true} = p := by
--     intro P e H
--     unfold Measure.real
--     simp [P, Prob, unif_edge_measure,Measure.toPMF_toMeasure]
--     sorry

-- def POW (base : Set α) : Set (Set α) := {A : Set α | A ⊆ base}
-- /-
-- # Expected Values (#Cycles smaller than l)#
-- Will be needed for various proofsteps
-- -/
-- /- Define sets of edges -/
-- abbrev edgesets := POW G.edgeSet → ℕ
-- noncomputable instance : Fintype (edgesets G) := by
--     unfold edgesets
--     have finApow : Finite (POW G.edgeSet) → ℕ := by
--         unfold POW
--     refine Fintype.ofFinite (↑(POW G.edgeSet) → ℕ))
-- instance : DiscreteMeasurableSpace (edgesets G) := by
--     exact MeasurableSingletonClass.toDiscreteMeasurableSpace


-- /-
-- # Expected Values (Max Independent Sets) #
-- Will be needed for various proofsteps
-- -/
```

```lean
/- # Probability 2 : Higher Order # -/
/- Create Higher Order Sample Space ΩK2 n of functions that maps "GRAPHS" to Bool -/
abbrev ΩK2 := (ΩK n) → Bool -- Type signature
noncomputable instance : Fintype (ΩK2 n) := by -- Is Fintype
  exact Pi.instFintype
instance : DiscreteMeasurableSpace (ΩK2 n) := by -- Is DiscreteMeasureSpace
  exact MeasurableSingletonClass.toDiscreteMeasurableSpace
/- Our base measure that maps a Graph to a probability -/
noncomputable def μB (f : ΩK n) : Measure (Bool) :=
  let p' := (EKpmf n p le_one f).toNNReal;
  have h : p' ≤ 1 := by {
    subst p'
    simp only [EKpmf]
    grw [PMF.coe_le_one]
    · simp only [ENNReal.toNNReal_one, le_refl]
    · simp only [ne_eq, ENNReal.one_ne_top, not_false_eq_true]
  }
  (PMF.bernoulli p' (h)).toMeasure
/- Using μB we define a measure over ΩK2 n-/
noncomputable abbrev ΩKμ : Measure (ΩK2 n) :=
  Measure.pi fun f : ΩK n ↦ (μB n p le_one f)
noncomputable instance : IsProbabilityMeasure (ΩKμ n p le_one) := by
  unfold ΩKμ
  have t : ∀ (i : ΩK n), IsProbabilityMeasure ((fun f ↦ μB n p le_one f) i) := by {
    intro f
    simp_all only [μB]
    infer_instance
  }
  exact Measure.pi.instIsProbabilityMeasure fun f ↦ μB n p le_one f
#check ΩKμ
/- FInally have a PMF over ΩK2 n -/
noncomputable def ΩKpmf : PMF (ΩK2 n) :=
  ((ΩKμ n p le_one) : Measure (ΩK2 n)).toPMF
```

```lean
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
```

```lean
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

namespace Theorems

/- # Theorems # -/

/- # ..Cycles # -/
/- TODO: Prove that there are exactly n choose k cycles of length l in a graph of size n
   NOTE that l is forced to be ≥3 !! This might be extremely hard :( -/
theorem CycleOfL_card : (CycleOfL n l).toFinset.card =
  Nat.choose n.1 l.1 * (Nat.factorial l.1) / (2 * l.1) := by sorry

/- # ..Probability i.e. 𝔼/ℙ # -/
/- The expected number of cycles with length l-/
noncomputable def E_CycleOfL : ℝ := ∑(C : CycleOfL n l), Pr_EsubG p n (Cycle_toEdgeset n C)

/- TODO: Prove that 𝔼[#cycles with length l] = n choose k * p^l -/
theorem Cycset_eq_card :
  E_CycleOfL n p l = Nat.choose n.1 l.1 * (Nat.factorial l.1) / (2 * l.1) * p.1^l.1
  := by sorry

end Theorems

/- Equivalence relation -/
@[scoped grind]
def PermEq (P1 P2 : Permutation n) :=
  P1.1 = P2.1 ∨ (P2.1 ∘ P1.1 = id ∧ P1.1 ∘ P2.1 = id)
-- PROPERTIES

/- Equivalence class of cycles -/
-- declare an instance of Setoid
private
instance PermutationSetoid : Setoid (Permutation n) where
  r := PermEq n
  iseqv := {
    refl := by grind only [PermEq];
    symm := by
      intros P1 P2 heq
      unfold PermEq at *; simp_all only [toFun_as_coe]
      obtain heq|heq := heq
      · left; simp only [heq]
      · right; simp_all only [and_self]
    trans := by
      intros P1 P2 P3 heq1 heq2
      unfold PermEq at *; simp_all only [toFun_as_coe]
      obtain heq1|heq1 := heq1
      · obtain heq2|heq2 := heq2
        · left;simp only [heq1, heq2]
        · right;rwa [←heq1] at heq2
      · obtain heq2|heq2 := heq2
        · right;rwa [heq2] at heq1
        · left;cases heq1;cases heq2
          rename_i hl hr hl' hr'
          exact Eq.symm (Function.LeftInverse.eq_rightInverse (congrFun hl') (congrFun hl))
  }
-- declare the equivalance class type
def Cycle := Quotient (PermutationSetoid n)

/-
abbrev PermListRel {n}{l}{S : SSn n l}(pl1 pl2 : PermList S) :=
  (PermListToPEK S) pl1 = (PermListToPEK S) pl2
-- PROPERTIES
-- If pl1 pl2 map to the same edgeset then they have the same length
theorem PermListRel_imp_eq_len {n}{l}(S : SSn n l) :
  ∀(pl1 pl2 : PermList S), (PermListRel pl1 pl2) → pl1.1.length = pl2.1.length := by
  intro pl1 pl2 pre;have t1 := pl1.3; have t2 := pl2.3; simp only [t1,t2]
-- If pl1 can be rotated by a k < l into pl2 then they will map to the same edgeset.
theorem PermList_rotate_imp_rel {n}{l}(S : SSn n l) :
  ∀(pl1 pl2 : PermList S), RotationalRel pl1 pl2 → (PermListRel pl1 pl2) := by
  unfold PermListRel RotationalRel; intro pl1 pl2 ⟨k,heq⟩
  ext e
  constructor
  · unfold PermListToPEK Conv.idxToPEK Conv.idxToEK
    simp only [Fin.getElem_fin, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index]
    intro idx h
    rw [←h]
    use ( ⟨(l.1 + idx.1 - k.1) % l.1,
      by refine Nat.mod_lt (l.val + ↑idx - ↑k) ?_;have := l.2;omega⟩)
    simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, SetLike.coe_eq_coe,
      Prod.swap_prod_mk, ←heq]
    left
    constructor
    · rw [List.getElem_rotate]; congr
      simp only [pl1.3, Nat.mod_add_mod]
      conv =>
        enter [1]
        rw [Nat.sub_add_cancel (by omega), Nat.add_mod_left, Nat.mod_eq_of_lt idx.is_lt]
    · rw [List.getElem_rotate]
      simp only [Conv.succ, Function.Embedding.coeFn_mk, Nat.mod_add_mod, pl1.3]
      conv =>
        enter [1,2]
        rw [add_assoc,add_comm 1,←add_assoc,Nat.sub_add_cancel (by omega)]
      by_cases cs : idx + 1 = l.1
      · conv => enter [1,2]; rw [add_assoc]
        simp only [cs, Nat.add_mod_right, Nat.mod_self]
      · have arith1 : idx + 1 < l.1 := by omega
        conv => enter[1,2]; rw [add_assoc]
        simp only [Nat.add_mod_left, Nat.mod_eq_of_lt arith1]
  · unfold PermListToPEK Conv.idxToPEK Conv.idxToEK
    simp only [Fin.getElem_fin, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index]
    intro idx h
    rw [←h]; simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      SetLike.coe_eq_coe, Prod.swap_prod_mk, ←heq]
    use ⟨ (idx.1 + k.1) % l.1, by refine Nat.mod_lt _ ?_;have := l.2;omega ⟩
    left
    constructor
    · rw [List.getElem_rotate]; congr; simp only [pl1.3]
    · rw [List.getElem_rotate]
      simp only [Conv.succ, Function.Embedding.coeFn_mk, Nat.mod_add_mod, pl1.3]
      conv => enter[1,2];rw [add_assoc,Nat.add_comm k,←add_assoc];
-- If pl1 can be reversed into pl2 then they will map to the same edgeset.
theorem PermList_reversion_imp_rel {n}{l}(S : SSn n l) :
  ∀(pl1 pl2 : PermList S), ReversionRel pl1 pl2 → (PermListRel pl1 pl2) := by
  intro pl1 pl2; unfold PermListRel ReversionRel; intro rel
  unfold PermListToPEK Conv.idxToPEK Conv.idxToEK
  ext e
  simp only [Fin.getElem_fin, Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ,
    Set.image_univ, Set.mem_range]
  have := l.2
  constructor
  · intro ⟨k,heq⟩; simp only [←rel]; rw[←heq]
    unfold Conv.succ; simp only [Function.Embedding.coeFn_mk, Subtype.mk.injEq, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, SetLike.coe_eq_coe, Prod.swap_prod_mk]
    use ⟨(l.1 + l.1 - 1 - (k + 1)) % l.1, by
      refine Nat.mod_lt (l.val + l.val - 1 - (↑k + 1)) ?_; omega ⟩;right
    simp only [List.getElem_reverse, pl1.3]
    constructor
    · congr
      by_cases cs : k.1 = l.1 -1
      · rw[cs]
        rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
        conv =>
          enter [1]
          rw [Nat.sub_add_comm (by linarith),Nat.add_sub_cancel]
        simp only [Nat.self_sub_mod, tsub_self]
      · have t : k + 1 ≤ (l.1 - 1) := by omega
        conv =>
          enter [1]
          rw [Nat.sub_add_comm (by omega),Nat.sub_add_comm (by omega)]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.sub_sub_self t]
        rw [Nat.mod_eq_of_lt (by omega)]
    · congr
      by_cases cs : k.1 = l.1 - 1
      · rw[cs]
        rw [Nat.sub_add_cancel (by omega)]
        conv =>
          enter [1,2]
          rw [Nat.sub_add_comm (by omega), Nat.add_sub_cancel]
          simp only [Nat.self_sub_mod]
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
        simp only [tsub_zero]
      · simp only [Nat.mod_add_mod]
        conv =>
          enter [1,2]
          rw [Nat.sub_add_eq, Nat.sub_add_cancel (by omega)]
          rw [Nat.add_sub_assoc (by omega), Nat.add_sub_assoc (by omega), Nat.add_mod_left]
          rw [Nat.mod_eq_of_lt (by omega)]
        grind only [cases eager Subtype, cases Or]
  · intro ⟨k,heq⟩; rw[←heq]; simp only [← rel,
      List.getElem_reverse, Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      SetLike.coe_eq_coe, Prod.swap_prod_mk]
    use ⟨l.val - 1 - (↑k + 1) % l.val, by
      refine Nat.sub_lt_of_lt ?_;omega⟩; right
    constructor
    · unfold Conv.succ; simp only [Function.Embedding.coeFn_mk, pl1.3]
    · unfold Conv.succ; simp only [Function.Embedding.coeFn_mk, pl1.3]
      congr
      by_cases cs : k = l.1 - 1
      · rw [cs]
        simp only [tsub_self]
        rw [Nat.sub_add_cancel (by omega),Nat.mod_self]
        simp only [tsub_zero]
        rw [Nat.sub_add_cancel (by omega),Nat.mod_self]
      · have : k + 1 < l.val := by omega
        conv =>
          enter [1]
          rw [Nat.mod_eq_of_lt (this)]
          rw [Nat.sub_add_eq, Nat.sub_add_cancel (by omega)]
        rw [Nat.mod_eq_of_lt (by omega)]
-- General Theorem of Permlist implications

-- If pl1 pl2 map to the same edgeset then either
-- pl1 can be rotated by a k < l into pl2 OR
-- pl1 can be reversed into pl2
theorem PermListRel_iff {n}{l}(S : SSn n l) :
  ∀(pl1 pl2 : PermList S),
  (PermListRel pl1 pl2) ↔ (RotationalRel pl1 pl2 ∨ ReversionRel pl1 pl2) := by
  sorry --[TODO]
-/

-- /- =============================================== -/
-- /- Rotational PermList Object -/

-- /- =============================================== -/

-- /- =============================================== -/
-- /- Bundle relation with proof that it is an equivalence relation -/
-- private
-- def CycleSetoid {n}{l}(S : SSn n l) : Setoid (PermList S) where
--   r := PermListRel
--   iseqv := {
--     refl := by grind
--     symm := by grind
--     trans := by grind
--   }
-- -- Properties
-- /- =============================================== -/

-- /- =============================================== -/
-- /- The Quotient Type of Cycles -/
-- def PEC {n}{l} (S : SSn n l) := Quotient (CycleSetoid S)
-- /- =============================================== -/
-- /- LIFTING FUNCTIONS -/
-- /- len of cycle (C) -/
-- def PEC_cyc_len {n}{l}{S : SSn n l}(C : PEC S) :=
--   Quotient.lift (fun c ↦ c.1.length) (PermListRel_imp_eq_len S) C


noncomputable
def Ecyc_len_one : ℝ :=
  ∑(S : SSn n l), Ecyc_ofPVK n p l S
noncomputable
def Ecyc_len_one' (p : ℙval)(n l : ℕ)(h0 : 0 < n)(h1 : 3 ≤ l)(h2 : l ≤ n) : ℝ :=
  let n : Nval := ⟨n, h0⟩;
  let l : Cval n := ⟨l,h1,h2⟩;
  Ecyc_len_one n p l
-- PROPERTIES
-- eval = (n choose l) * l!/(2l) * p^l
@[simp, grind =]
theorem Ecyc_len_one_eval :
  Ecyc_len_one n p l = n.1.choose l.1 * l.1.factorial / (2 * l.1) * p.1^(l.1) := by
  unfold Ecyc_len_one; simp only [Finset.univ_eq_attach, Ecyc_ofPVK_eval, Finset.sum_const,
    Finset.card_attach, nsmul_eq_mul]
  rw [SSn_card]
  grind only [cases eager Subtype]
/- =============================================== -/
/- Expected number of cycles with length ≤ maxl -/
noncomputable
def E_cycle_len_le (n : Nval) (maxl : ℕ) :=
  ∑(i : {i : Cval n // i.1 ≤ maxl}),∑(S : SSn n i),∑(C : Cycle S), Pr_EsubG p n (CycleToPEK C)
-- eval to some sum
@[simp]
theorem E_cycle_len_le_eval (n : Nval) (maxl : ℕ) :
  E_cycle_len_le p n maxl =
    ∑(i : {i : Cval n // i.1 ≤ maxl}),
    n.1.choose i.1.1 * i.1.1.factorial / (2 * i.1.1) * p.1^(i.1.1) := by
  unfold E_cycle_len_le
  simp only [PrE_subs, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_pow]
  congr
  ext l
  rw [←Ecyc_len_one_eval n p l.1]
  unfold Ecyc_len_one
  congr
  ext S
  unfold Ecyc_ofPVK
  congr
  ext C
  simp only [Ecyc_len_eval]
  congr
  convert CycleToPEK_toCard C; exact Set.ncard_eq_toFinset_card' (CycleToPEK C)

  /- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
   We shall assume Linearity of expected values
   !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! -/
/- =============================================== -/
/- Expected number of length l cycles given a Vertex set-/
noncomputable
def Ecyc_ofPVK (S : SSn n l) : ℝ :=
  ∑(C : Cycle S), Ecyc_one n p l S C
-- PROPERTIES
-- eval = l!/(2l) * p^l
@[simp, grind =]
theorem Ecyc_ofPVK_eval (S : SSn n l) :
  Ecyc_ofPVK n p l S = l.1.factorial / (2 * l.1) * p.1^(l.1) := by
  unfold Ecyc_ofPVK
  simp only [Ecyc_len_eval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_eq_mul_right_iff,
    pow_eq_zero_iff', NNReal.coe_eq_zero, ne_eq]
  left
  rw [Cycle_univ_card S, mul_comm l.1]
  obtain ⟨l,lp,bound⟩ := l
  simp_all only
  rw [Nat.cast_div]
  pick_goal 2; {
    clear S bound
    induction' lp with l bd ih
    · simp only [Nat.reduceMul, Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd, zero_add,
      mul_one, dvd_refl]
    · unfold Nat.factorial
      rw [mul_comm]
      refine Nat.mul_dvd_mul ?_ ?_
      · simp only [Nat.succ_eq_add_one, dvd_refl]
      · exact dvd_of_mul_right_dvd ih
  }
  pick_goal 2; { by_contra cnt; push_cast at cnt; simp_all only [mul_eq_zero, OfNat.ofNat_ne_zero,
    Nat.cast_eq_zero, false_or]; subst cnt; contradiction }
  push_cast; rfl
```