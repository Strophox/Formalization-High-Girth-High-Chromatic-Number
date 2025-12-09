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
