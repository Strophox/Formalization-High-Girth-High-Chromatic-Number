## Formalizing a Theorem (Erdős 1959) about the Existence of Graphs with High Girth and High Chromatic Number in Lean 4

This repo hosts the source code of a project which works to formalize the following mathematical theorem, initially proved by Paul Erdős:

> **Theorem (Erdős 1959).**\
> For all k,l ∈ ℕ, there exists a graph G with γ(G) > l and χ(G) > k.

Or as currently formulated in Lean 4;

```lean
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring

theorem high_girth_high_chromatic_number (k : ℕ) (l : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.egirth > l ∧ G.chromaticNumber > k
```
