import Formalization.API_Probability
import Formalization.API_IndSets
import Formalization.API_Cycles

import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring


--import Formalization.Probability

set_option autoImplicit false
-- set_option tactic.hygienic false
set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.induction false

open API_ℙ API_𝕀 API_ℂ Real
open scoped API_ℙ API_ℂ API_𝕀 NNReal Real

/-===============================================================-/
/- Start of part 1 -/
#print E_cycle_ofLen_le -- our 𝔼
lemma P1_1 (p : ℙval)(n l : ℕ)(h0 : 0 < n) :
let N : API_𝔾.Nval := ⟨n,h0⟩;
  E_cycle_ofLen_le p N l ≤ (l:ℝ) * ((n:ℝ) * p.1.toReal)^(l:ℝ) := by
  -- PROOF STARTS HERE
  intro N; rw [E_cycle_ofLen_le_eval]
  -- [TODO]
  sorry
/-===============================================================-/
/- Intermission where Markov inequality is used then Back to normal probability -/

-- Probability that the number of cycles with l ≤ maxl is ≥ minc
#print Pr_cycles_count_le_ge

lemma P1_2 (p : ℙval)(maxl minc : ℕ)(hminc : minc > 0):
∀(n : ℕ)(h : 0 < n), let N : API_𝔾.Nval := ⟨n,h⟩; ∃(c : ℝ),
  Pr_cycles_count_le_ge p N maxl minc ≤ 2 * maxl * n^(-c) := by
  -- PROOF STARTS HERE
  intro n np N
  grw [EcycToPcyc_markov]; pick_goal 2; {linarith}
  -- [TODO]
  sorry
/-===============================================================-/
/- LIMITS PROOF -/
-- [TODO]
/-===============================================================-/

/-===============================================================-/
/- Start of part 2 -/
lemma P2_1 (p : ℙval)(n sz : ℕ)(h : 0 < n):
let N : API_𝔾.Nval := ⟨n,h⟩;
  (PrI_αG_gt p N sz) ≤ rexp 0 / sz.factorial := by
  -- PROOF STARTS HERE
  intro N; grw [UB_PrI_αG_gt]
  --[TODO]
  sorry

/- LIMITS PROOF -/
-- [TODO]
/-===============================================================-/

theorem high_girth_high_chromatic_number (k : ℕ) (l : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.egirth > l ∧ G.chromaticNumber > k := by

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
  --#  ∀ ε>0, ∃ n₂, P[α(G) ≥ x(n₂)] < ε                                      by:def lim?

  --#  choose n = max(n₁, n₂), ε = 0.5  ⇝  G with P[X ≥ n₁/2] + P[α(G) ≥ x(n₂)] < 0.5 + 0.5    by:apply previous two stmts
  /- ^^^ Easily done! Classical.choose f from complement ^^^-/
  /- Show that for every cycle, removing a vertex x from a cycle v -> u x v -> u means either
     - there exist no other u -> v - disjoint path meaning cycle length of infinity
     - there exist another u -> v disjoint path meaning the cycle length has increased
       if their length <= l then we also remove a vertex from there -/
  --## let G' := "G but with n/2 nodes removed  ⇝  there are no more small cycles"
  /- directly follows from eliminating all cycles of length ≤ l -/
  --## "G' has girth greater than l"                                                           by:facts and logic

  -- Prove that all independent sets in a graph either shrink or stay the same when taking away any vertex
  --## α(G') ≤ α(G)                            by:facts and logic
  --#  α(G') < x                               by:choice of n
  --#  α(G') < ⌈3/p * ln(n)⌉                   by:rw x

  /- Have vertex sets that are coloured the same
     They are all independent sets.
     Choose the biggest * #of colors. EZ -/
  --## χ(G') * α(G') ≥ |G'|                    by:facts and logic
  --#  χ(G') ≥ |G'| / α(G')                    by:reorder
  --#  χ(G') ≥ (n/2) / α(G')                   by:def G'
  --#  χ(G') ≥ (n/2) / ⌈3/p * ln(n)⌉           by:grw α(G') < ⌈3/p * ln(n)⌉
  --#  χ(G') ≥ (n/2) / ⌈3/n^(θ - 1) * ln(n)⌉   by:rw p
  /- ANOTHER LIMITS INTO CLASSICAL CHOOSE -/
  --## lim n → ∞: χ(G') → ∞                    by: ??? this step REALLY sucks, we might have to choose a different 'x' to begin with
  --#  ∀ m, ∃ nₓ, χ(G') > m                    by:def lim?

  --#  adjust n = max(n, nₓ)  ⇝  χ(G') > k     by:apply previous stmt
  --# Qed.

  sorry
