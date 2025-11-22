
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
    # {g : G(n,p) | X g ≥ n/2 } ≤ (∫⁻ (g : G(n,p)), f g ∂#) / (n/2)
```

So we specifically see that we need:
* `G(n,p)` to be a `MeasureableSpace`,
* a counting measure(?) `# : Measure G(n,p)`,
* that `AEMeasurable X #`.

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