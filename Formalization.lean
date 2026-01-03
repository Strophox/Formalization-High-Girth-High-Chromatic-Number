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

open API_ℙ API_𝕀 API_ℂ Real
open scoped API_ℙ API_ℂ API_𝕀 NNReal

/- WHACKY THETA -/
structure Theta {n} (lmax : Cval n) where
  val : ℝ≥0
  lt : val < 1 / (lmax.1 : ℝ)
variable {n}{lmax : Cval n}(θ : Theta lmax)
/- WHACKY PROBABILITY -/
noncomputable
def pθ {n}{lmax : Cval n}(θ : Theta lmax) : ℙval :=
⟨((n.1 : ℝ)^((θ.1 : ℝ) - 1)).toNNReal,
  by
  simp only [toNNReal_le_one]
  obtain ⟨n,np⟩ := n;obtain ⟨θ,tp⟩ := θ;obtain ⟨l,l1,l2⟩ := lmax; simp_all only
  grw [tp]
  pick_goal 2; {simp only [Nat.one_le_cast]; omega}
  simp_all only
  have : 1/3 ≥ 1/(l : ℝ) := by
    simp only [one_div, ge_iff_le]
    refine inv_anti₀ (by linarith) (by simp only [Nat.ofNat_le_cast, l1])
  grw [←this]
  pick_goal 2; {simp only [Nat.one_le_cast]; omega}
  refine (rpow_le_one_iff_of_pos ?_).mpr ?_
  · simp only [Nat.cast_pos, np]
  · left; constructor
    · simp only [Nat.one_le_cast]
      omega
    · simp only [one_div, tsub_le_iff_right, zero_add]
      refine inv_le_one_iff₀.mpr (by right;exact Nat.one_le_ofNat) ⟩

/- Start of part 1 -/
lemma P1_1 (n : Nval) (lmax : Cval n) (θ : Theta lmax) :
  Ecyc_len_range_le (pθ θ) lmax ≤ lmax.1 * n.1^((θ.1: ℝ) * lmax.1) := by
  unfold Ecyc_len_range_le
  simp only [Ecyc_len_one_eval, Nat.cast_add, Nat.cast_ofNat]
  -- less go
  sorry
/- Intermission where Markov inequality is used then Back to normal probability -/
-- [TODO]
/- LIMITS PROOF into Axiom of choice (MUST USE CLASSICAL CHOOSE) -/
-- [TODO]

/- Start of part 2 -/
lemma P2_1 (n : Nval) (p : ℙval) (sz : SZval n) :
  (PrI_ofsz n p sz) ≤ (exp 0) / (sz.val.factorial) := by
  grw [PrI_ofsz_UBval]
  -- Less Go (exp 1) is Eulers Number
  sorry
/- LIMITS PROOF into Axiom of choice (MUST USE CLASSICAL CHOOSE) -/
-- [TODO]

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
