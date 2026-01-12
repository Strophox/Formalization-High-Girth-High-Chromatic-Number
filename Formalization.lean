import Formalization.API_Probability
import Formalization.API_IndSets
import Formalization.API_Cycles

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Analysis.SpecialFunctions.Exp


--import Formalization.Probability

set_option autoImplicit false
-- set_option tactic.hygienic false
set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.induction false

open API_ℙ API_𝕀 API_ℂ Real
open scoped API_ℂ API_𝕀 NNReal Real

/-===============================================================-/
/- Start of part 1 -/
#print E_cycle_ofLen_le -- our 𝔼
lemma P1_1 (p : ℙval)(n l : ℕ):
∀(n : ℕ)(h : 0 < n), let N : API_𝔾.Nval := ⟨n,h⟩;
  E_cycle_ofLen_le p N l ≤ (l:ℝ) * ((n:ℝ) * p.1.toReal)^(l:ℝ) := by
  -- PROOF STARTS HERE
  intro n h N; rw [E_cycle_ofLen_le_eval]
  -- [TODO]
  sorry
/-===============================================================-/
/- Intermission where Markov inequality is used and then
   back to normal probability -/

-- Probability that the number of cycles with l ≤ maxl is ≥ minc
#print Pr_cycles_count_le_ge
-- The cycle with length ≤ maxl counter
#print G_cycles_oflen_le_count

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
/- Part 2 : "largest independent set of G" -/
/- HELPER LEMMA -/
lemma rexp_UB : rexp 1 ≤ 3 := by
  sorry
/-REWRITING
  ## Pr[α(G) ≥ x] ≤ choose(n,x)                * (1 - p)^choose(x,2)       by:that's just how it is
  #  Pr[α(G) ≥ x] ≤ ( n * ⋯ * n-(x-1) )/( x! ) * (1 - p)^(x*(x-1)/2)       by:def choose
  #  Pr[α(G) ≥ x] ≤ ( n * ⋯ * n-(x-1) )/( x! ) *  e^(-p)^(x*(x-1)/2)       by:recall e^x := 1 + x + x^2/4 + …
  #  Pr[α(G) ≥ x] ≤ ( n^x             )/( x! ) *  e^(-p)^(x*(x-1)/2)       by:round
  #  Pr[α(G) ≥ x] ≤ ( e^(ln(n) * x)   )/( x! ) *  e^(-p)^(x*(x-1)/2)       by:n = e^ln(n)
  #  Pr[α(G) ≥ x] ≤ ( e^(ln(n) * x)   )/( x! ) *  e^(-p/2 * (x-1) * x)     by:reorder
  #  Pr[α(G) ≥ x] ≤ e^( ln(n) * x + -p/2 * (x-1) * x )/( x! )              by:reorder
  #  Pr[α(G) ≥ x] ≤ e^( ln(n) - p/2 * (x-1)      )^x / ( x! )              by:reorder
  #  Pr[α(G) ≥ x] ≤ e^( ln(n) - p/2 * (⌈3/p * ln(n)⌉-1)      )^x / ( x! )  by:rw x
  ## Pr[α(G) ≥ x] ≤ e^0  / ( x! )                                          by:magic -/
lemma P2_1 (p : ℙval)(n : ℕ)(h : 3 ≤ n)(h' : p.1 ≠ 0):
let N : API_𝔾.Nval := ⟨n,by linarith⟩;
let sz : ℕ := ⌈3 / p.1 * log n⌉.toNat;
  (PrI_αG_gt p N sz) ≤ rexp 0 / sz.factorial := by
  -- PROOF STARTS HERE
  intro N sz; grw [UB_PrI_αG_gt]
  conv => enter [1,2,2]; rw [Nat.choose_two_right]
  conv => enter [1,1,1]; rw [Nat.choose_eq_descFactorial_div_factorial]
  subst N; simp only
  have arith : (1 - ↑p.val) ≤ rexp (-p.1) := by
    exact one_sub_le_exp_neg ↑p.val
  grw [arith];
  pick_goal 2; { simp only [sub_nonneg, NNReal.coe_le_one, p.2] }
  clear arith; rw [←exp_nat_mul, Nat.cast_div]
  pick_goal 2; { exact Nat.factorial_dvd_descFactorial n sz }
  pick_goal 2; { simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.factorial_ne_zero sz }
  have arith : n.descFactorial sz ≤ n^sz := by
    exact Nat.descFactorial_le_pow n sz
  grw[arith];clear arith
  have arith : n^sz = rexp (log n * sz) := by
    rw [exp_mul,exp_log];
    · simp only [rpow_natCast]
    · simp only [Nat.cast_pos]; linarith
  norm_cast
  simp only [Nat.cast_pow, arith,div_mul_eq_mul_div]; clear arith
  rw [←exp_add,Nat.cast_div]
  pick_goal 2; {
    induction sz
    · simp only [zero_tsub, mul_zero, dvd_zero]
    · rename_i n' ih; rw [Nat.add_sub_cancel, mul_comm]
      exact Nat.two_dvd_mul_add_one n'
  }
  pick_goal 2; { push_cast;exact Ne.symm (NeZero.ne' 2) }
  rw [Nat.cast_mul, div_mul_comm, mul_comm sz.cast, ←mul_assoc, ←add_mul, exp_mul]

  have arith0 : ⌈3 / p.1 * log n⌉.toNat = ⌈3 / p.1 * log n⌉ := by
    simp only [Int.ofNat_toNat, sup_eq_left]
    positivity
  have arith1 : (⌈3 / p.1 * log n⌉.toNat : ℝ) = ⌈3 / p.1 * log n⌉ := by
    norm_cast
  subst sz; generalize x : ⌈3 / p.1 * log n⌉.toNat = sz
  rw [neg_div,neg_mul_comm,Nat.cast_sub,neg_sub]
  pick_goal 2; {
    subst x
    zify
    rw [arith0]
    refine Int.le_ceil_iff.mpr ?_
    simp only [Int.cast_one, sub_self]
    have : log n > 0 := by refine log_pos ?_; simp only [Nat.one_lt_cast]; linarith
    positivity
  }
  rw [mul_sub,←add_sub_assoc]; norm_cast; rw [mul_one]
  nth_rw 1 [←x]
  -- SECTION
  have arith :
    (log ↑n + ↑(p.val / 2) - ↑(p.val / 2 * ↑⌈3 / ↑p.val * log ↑n⌉.toNat)) ≤ 0 := by {
      refine sub_nonpos.mpr ?_
      push_cast
      rw [arith1]
      refine (div_le_iff₀' ?_).mp ?_
      { positivity }
      rw [add_div,div_self]
      pick_goal 2; { positivity }
      rw [<-div_mul]
      trans; pick_goal 2; { apply Int.le_ceil}
      rw [div_mul_comm]; refine add_le_of_le_tsub_left_of_le ?_ ?_
      { gcongr; linarith }
      rw [←sub_mul,←sub_div]; norm_num1
      refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · have := p.2; grw [this]; simp only [NNReal.coe_one, ne_eq, one_ne_zero, not_false_eq_true,
        div_self, le_refl]
      · refine (le_log_iff_exp_le ?_).mpr ?_
        · simp only [Nat.cast_pos]; linarith
        · grw [←h]
          simp only [Nat.cast_ofNat]
          exact rexp_UB
    }
  grw [arith]; simp only [exp_zero, one_pow, one_div, le_refl]
/-===============================================================-/
/- LIMITS PROOF
   ## lim n → ∞: Pr[α(G) ≥ x] → 0                                           by: ??? -/
lemma P2_2 (p : ℙval)(hp : p.1 ≠ 0) :
  Filter.Tendsto (fun n : { n : ℕ // n > 0 } ↦ (PrI_αG_gt p ⟨n.1,n.2⟩ ⌈3 / p.1 * log n.1⌉.toNat) )
  Filter.atTop (nhds 0)
  := by
  have lowerbound :
    (Filter.Tendsto (fun n : { n : ℕ // n > 0 } ↦ (0 : ℝ) ) Filter.atTop (nhds 0) ) := by
    exact tendsto_const_nhds
  have upperbound :
    (Filter.Tendsto (fun n : { n : ℕ // n > 0 } ↦ 1 / (⌈3 / p.1 * log n.1⌉.toNat.factorial : ℝ)) Filter.atTop (nhds 0) ) := by
    simp only [one_div]
    apply Filter.Tendsto.inv_tendsto_atTop

    have h : ∀ (n : {n : ℕ // n > 0}),
    (fun n ↦ ⌈3 / p.val * log n.1⌉.toNat) n ≤ (fun n ↦ (⌈3 / p.val * log n.1⌉.toNat.factorial : ℝ) ) n := by
      intro n; simp only; norm_cast; exact Nat.self_le_factorial _

    have mono : Monotone (fun n : {n : ℕ // n > 0} ↦ (⌈3 / p.val * log n.1⌉.toNat : ℝ)) := by {
      intro ⟨a,a'⟩ ⟨b,b'⟩ od; simp only
      gcongr; rw [Int.toNat_le]
      have arith0 : ⌈3 / p.1 * log b⌉.toNat = ⌈3 / p.1 * log b⌉ := by
        simp only [Int.ofNat_toNat, sup_eq_left]
        positivity
      rw [arith0]
      have arith : a ≤ b := by omega
      grw [arith]
    }

    apply Filter.tendsto_atTop_mono h
    simp only
    apply Filter.tendsto_atTop_atTop_of_monotone mono
    intro x
    have arith0 :∀(n : {n : ℕ // n > 0}), (⌈3 / p.1 * log n⌉.toNat : ℝ) = ⌈3 / p.1 * log n⌉ := by
      intro n; norm_cast; simp only [NNReal.coe_div, NNReal.coe_ofNat, Int.ofNat_toNat, sup_eq_left]
      positivity
    conv => enter [1];ext x';enter[2]; rw [arith0 x']

    use (⟨⌈rexp (x * p.1 / 3)⌉.toNat,by simp;positivity⟩)
    simp only
    have arith : ⌈rexp (x * ↑p.1 / 3)⌉.toNat = ⌈rexp (x * ↑p.1 / 3)⌉ := by
      symm
      rw [Int.eq_natCast_toNat]
      positivity
    have arith' : (⌈rexp (x * ↑p.1 / 3)⌉.toNat : ℝ) = ⌈rexp (x * ↑p.1 / 3)⌉ := by
      symm
      norm_cast
      rw [arith]
    rw [arith']
    trans; pick_goal 2; { apply Int.le_ceil }
    grw [←Int.le_ceil (rexp (x * ↑p.val / 3))]
    rw [log_exp]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_div_cancel₀']
    rw [mul_div_assoc, div_self, mul_one]
    simp only [ne_eq, NNReal.coe_eq_zero, hp, not_false_eq_true]

  have ne : Nonempty {n : ℕ // n > 0} := by {
    refine nonempty_subtype.mpr ?_; use 1; linarith }
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowerbound upperbound ?_ ?_
  · rw [Filter.eventually_atTop]
    use ⟨1,by linarith⟩
    intro n bound
    unfold PrI_αG_gt
    positivity
  · rw [Filter.eventually_atTop]
    use ⟨3,by linarith⟩
    intro n bound
    have ineq := P2_1 p n bound hp
    simp only at ineq
    grw [ineq]
    simp only [exp_zero, one_div, le_refl]
/- EXTRACTOR
   #  ∀ ε>0, ∃ n₂, P[α(G) ≥ x(n₂)] < ε                                      by:def lim? -/
lemma P2_Extractor (p : ℙval)(hp : p.1 ≠ 0):
  ∀(eps : ℝ)(_ : eps > 0), ∃(n : ℕ)(h : n > 0),
    PrI_αG_gt p ⟨n,h⟩ ⌈3 / p.1 * log n⌉.toNat < eps := by
  intro eps bde
  have prev := P2_2 p hp
  have : Nonempty { n : ℕ // n > 0 } := by
    refine nonempty_subtype.mpr ?_; use 1; linarith
  rw [Metric.tendsto_atTop] at prev
  specialize (prev eps (by linarith))
  obtain ⟨⟨n,np⟩,prev⟩ := prev
  use n, np; specialize prev ⟨n,np⟩ (by rfl)
  simp only [dist_zero_right, norm_eq_abs] at prev
  rw [abs_of_nonneg] at prev
  pick_goal 2; { unfold PrI_αG_gt; exact MeasureTheory.measureReal_nonneg }
  assumption
/-===============================================================-/

/-===============================================================-/
/- PART 3 -/
/-===============================================================-/

/-===============================================================-/
/- THE EXTRACTION-/
/- If probability < 1 then there exists a graph in the complement -/
theorem anti_graph_exists (p : ℙval) (n : API_𝔾.Nval) :
  ∀(F : Set (ΩK n)), (EKμ p n).real F < 1 →  ∃f, f ∈ Fᶜ := by {
    intro F h
    by_contra cnt; simp only [Set.mem_compl_iff, not_exists, not_not] at cnt
    have t : F = Set.univ := by exact Set.eq_univ_of_univ_subset fun ⦃a⦄ a_1 ↦ cnt a
    have t0 : (EKμ p n).real F = 1 := by rw [t];exact MeasureTheory.measureReal_univ_eq_one
    rw [t0] at h; simp only [lt_self_iff_false] at h
  }
/- Gives us a graph G for which α(G) < sz and which has < minc cycles of length ≤ maxl.
   Given that the probabilities of both add up to ≤ n and that both graphs are defined on
   n vertices!
# choose n = max(n₁, n₂), ε = 0.5  ⇝  G with P[X ≥ n₁/2] + P[α(G) ≥ x(n₂)] < 0.5 + 0.5 -/
theorem anti_graph (p : ℙval) (n : ℕ)(h : 0 < n) (maxl minc sz : ℕ) :
  let N : API_𝔾.Nval := ⟨n,h⟩;
  Pr_cycles_count_le_ge p N maxl minc < 1/(2 : ℝ) →
  PrI_αG_gt p N sz < 1/(2 : ℝ) →
  ∃(f : ΩK N), G_cycles_oflen_le_count f maxl < minc ∧ αG f < sz := by
  intro N pr1 pr2
  unfold Pr_cycles_count_le_ge at pr1; simp only at pr1
  unfold PrI_αG_gt at pr2
  set M := (EKμ p N).real
  set F1 := {f | G_cycles_oflen_le_count f maxl ≥ minc}
  set F2 := (G_αG_ge N sz)
  have t0 : M (F1 ∪ F2) ≤ M F1 + M F2 := by exact MeasureTheory.measureReal_union_le F1 F2;
  have t1 : M F1 + M F2 < 1 := by linarith
  grw [←t0] at t1
  apply ( anti_graph_exists p N (F1 ∪ F2) ) at t1
  clear pr1 pr2 t0
  obtain ⟨af,t1⟩ := t1
  simp only [Set.compl_union, Set.mem_inter_iff] at t1; obtain ⟨s1,s2⟩ := t1
  -- rewrite them back into sets
  use af
  constructor
  · subst F1
    simp only [Set.mem_setOf_eq, ge_iff_le, Set.mem_compl_iff, not_le] at s1
    assumption
  · subst F2
    rw [
      ←Set.mem_setOf_eq (p := fun f ↦ αG f < sz),
      ←G_αG_lt,
      αG_lt_eq_ge_complement
    ]; assumption
/-===============================================================-/
--#  let x := ⌈3/p * ln(n)⌉
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

  -- [TODO] pass NON_ZERO probability into P2_Extractor
  have P2 := P2_Extractor sorry sorry (1/2) (by linarith)
  obtain ⟨n2,bd2,P2⟩ := P2


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

  /- ANOTHER LIMITS -/
  --## lim n → ∞: χ(G') → ∞                    by: ??? this step REALLY sucks, we might have to choose a different 'x' to begin with
  --#  ∀ m, ∃ nₓ, χ(G') > m                    by:def lim?

  --#  adjust n = max(n, nₓ)  ⇝  χ(G') > k     by:apply previous stmt
  --# Qed.

  sorry
