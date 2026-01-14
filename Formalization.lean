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
/- #  let θ < 1 / l
   #  let p := n^(θ - 1) -/
noncomputable
def pt (n : API_𝔾.Nval)(l : ℕ)(θ : ℝ≥0)(_ : θ < 1 / (l : ℝ)) : ℙval :=
  ⟨((n.1)^( (θ : ℝ) - (1 : ℝ) ) : ℝ≥0),by
    rename_i bd; grw[bd]
    pick_goal 2; { have := n.2;simp only [Nat.one_le_cast, ge_iff_le];omega }
    have : ( (1 / l.cast ) - 1 : ℝ ) ≤ 0 := by
      simp only [one_div, tsub_le_iff_right, zero_add]
      exact Nat.cast_inv_le_one l
    grw [this]
    pick_goal 2; { have := n.2;simp only [Nat.one_le_cast, ge_iff_le];omega }
    simp only [NNReal.rpow_zero, le_refl]
  ⟩
/- ## E[X] = ∑ᵢ₌₃ˡ p^i         * ( n * (n-1) * ⋯ * (n-(i-1)) )/( 2*i )  by:facts and logic
   #  E[X] ≤ ∑ᵢ₌₃ˡ n^(θ*i - i) * n^i                                    by:round up
   #  E[X] ≤ ∑ᵢ₌₃ˡ n^(θ*i)                                              by:cancel
   #  E[X] ≤ ∑ᵢ₌₃ˡ n^(θ*l)                                              by:round up
   #  E[X] ≤ l * n^(θ*l)                                                by:sum of constants -/
lemma P1_1 (l : ℕ)(θ : ℝ≥0)(hθ : θ < 1 / (l : ℝ)):
∀(n : ℕ)(h : 0 < n),
  let N : API_𝔾.Nval := ⟨n,h⟩;
  let p := pt N l θ hθ
  E_cycle_ofLen_le p N l ≤ (l:ℝ) * n ^ ( θ * l : ℝ ) := by
  -- PROOF STARTS HERE
  intro n h N p; rw [E_cycle_ofLen_le_eval]
  subst p; unfold pt; simp only
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat,
    NNReal.coe_pow, NNReal.coe_rpow]
  calc
    ∑ i : {i : Cval N // i.1 ≤ l},
    ↑(N.val.choose i.1.1) * i.1.1.factorial / (2 * i.1.1) * ( (N.1:ℝ) ^ ( (θ:ℝ) - 1)) ^ i.1.1
    _ ≤ ∑ i : {i : Cval N // i.1 ≤ l},
        (n:ℝ)^( (θ:ℝ) * i.1.1 - i.1.1) * (n:ℝ)^(i.1.1:ℝ) := by {
          subst N; simp only; apply Finset.sum_le_sum
          intro i tr
          obtain ⟨⟨i,ip1,ip2⟩,ip3⟩ := i
          simp only at ip2; simp only at ip3; simp only
          conv =>
            enter [1,2]; rw [←rpow_mul_natCast (by norm_cast;linarith),sub_mul,mul_comm 1, mul_one]
          conv => enter [2]; rw [mul_comm]
          rw [mul_le_mul_iff_left₀ (by positivity)]
          rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div]
          pick_goal 2; { exact Nat.factorial_dvd_descFactorial n i }
          pick_goal 2; { norm_cast; exact Nat.factorial_ne_zero i }
          conv =>
            enter [1,1]; rw [div_mul,div_self (by norm_cast;exact Nat.factorial_ne_zero i),div_one]
          refine (div_le_iff₀ ?_).mpr ?_
          { norm_cast;linarith }
          clear tr ip2 ip3
          induction' ip1 with i' ip3' ih
          · simp only [Nat.descFactorial_succ, tsub_zero, Nat.descFactorial_zero, mul_one,
            Nat.cast_mul, Nat.cast_ofNat]
            norm_num; grw [show n - 1 ≤ n from by omega, show n - 2 ≤ n from by omega]
            norm_cast; nlinarith
          · simp only [Nat.le_eq] at ip3'
            simp only [Nat.succ_eq_add_one, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_add,
              Nat.cast_one]
            grw [ih]
            rw [rpow_add,rpow_one]
            pick_goal 2; {norm_cast}
            rw [←mul_assoc]
            conv => enter [2]; rw [( mul_comm _ (n:ℝ) )]
            grw [show n - i' ≤ n from by omega, mul_le_mul_iff_right₀
              ( by norm_cast;positivity )]
            norm_cast; linarith
        }
      _ ≤ ∑ i : {i : Cval N // i.1 ≤ l},(n:ℝ)^( (θ:ℝ) * i.1.1 ) := by {
        apply Finset.sum_le_sum; intro i tr
        conv => enter [1]; rw [←rpow_add (by norm_cast), sub_add_cancel]
      }
      _ ≤ ∑ i : {i : Cval N // i.1 ≤ l},(n:ℝ)^( (θ:ℝ) * l ) := by {
        apply Finset.sum_le_sum; intro ⟨⟨i,p1,p2⟩,ip⟩ tr
        simp only
        apply rpow_le_rpow_of_exponent_le
        · norm_cast
        · simp only at ip
          by_cases cs : θ > 0
          · rw [mul_le_mul_iff_right₀]
            pick_goal 2; { norm_cast }
            norm_cast
          · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at cs
            subst cs; norm_num
      }
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_le_mul_iff_left₀]
  pick_goal 2; { positivity }
  simp only [Nat.cast_le]
  conv => enter [2]; rw [show l = Fintype.card (Fin l) from by exact Eq.symm (Fintype.card_fin l)]
  refine Fintype.card_le_of_injective
    (fun i ↦ ⟨i.1.1 - 1,by have t:=i.2;have:=i.1.2;omega⟩)
    ( by
      intro ⟨⟨a,a1,a2⟩,ap⟩ ⟨⟨b,b1,b2⟩,bp⟩
      simp only [Fin.mk.injEq, Subtype.mk.injEq, Cval.mk.injEq]
      intro heq
      omega
    )
/-===============================================================-/
/- Intermission where Markov inequality is used and then
   back to normal probability
   #  P[X ≥ n/2] ≤ E[X] / (n/2)                                         by:Markov Inequality
   #  P[X ≥ n/2] ≤ l * n^(θ*l) / (n/2)                                  by:grw E[X] ≤ l * n^(θ*l)
   #  P[X ≥ n/2] ≤ 2 * l * n^(θ*l - 1)                                  by:reorder
   #  P[X ≥ n/2] ≤ 2 * l * n^(-constant)                                by:recall θ<1/l ⇒ θ*l < 1 -/
lemma P1_2 (l: ℕ)(θ : ℝ≥0)(hθ : θ < 1 / (l : ℝ)) :
∀(n : ℕ)(h : 0 < n), let N := ⟨n,h⟩; let p := pt N l θ hθ
  Pr_cycles_count_le_ge p N l (⌈n/(2:ℝ)⌉.toNat) ≤ 2 * l * (n:ℝ)^( θ.toReal * l - 1 ) := by
  -- PROOF STARTS HERE
  intro n np N p
  grw [EcycToPcyc_markov]
  pick_goal 2; {
    simp only [gt_iff_lt, Int.lt_toNat, CharP.cast_eq_zero, Int.ceil_pos, Nat.ofNat_pos,
      div_pos_iff_of_pos_right, Nat.cast_pos]
    exact np
  }
  subst N
  have tmp := P1_1 l θ hθ n np; simp only at tmp
  grw [tmp]; clear tmp
  calc
    ↑l * ↑n ^ ( θ.toReal * l ) / ⌈ (n:ℝ) / 2 ⌉.toNat
      ≤ 2 * l * (n : ℝ)^( θ.toReal * l - 1 ) := by {
        refine (div_le_iff₀' ?_).mpr ?_
        { norm_cast;rw [Int.ceil_toNat]
          zify
          rw [Int.natCast_ceil_eq_ceil ( by positivity )]
          positivity
        }
        conv => enter [2]; rw [mul_comm, mul_assoc, mul_comm 2,mul_assoc]
        conv =>
          enter [2,2,2,2]
          rw [show ⌈(n:ℝ) / 2⌉.toNat.cast = ⌈(n:ℝ) / 2⌉.cast from by
            norm_cast
            rw [Int.ceil_toNat,Int.natCast_ceil_eq_ceil (by positivity) ]
          ]
        by_cases cs : l > 0
        · rw [mul_le_mul_iff_right₀ (by positivity)]
          rw [rpow_sub (by positivity), rpow_one, ←mul_assoc, mul_comm 2, div_mul_comm ]
          nth_rw 3 [mul_comm]; rw [mul_assoc]
          have t : 1 ≤ (2 / (n : ℝ) * ⌈(n:ℝ) / 2⌉) := by
            refine (inv_le_iff_one_le_mul₀' ?_).mp ?_
            { positivity }
            simp only [inv_div]
            exact Int.le_ceil ((n:ℝ) / 2)
          grw [←t]
          rw [mul_one]
        · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at cs
          subst cs; norm_num
      }
lemma P1_2_bd_lt :
∀(l: ℕ)(θ : ℝ≥0)(_ : θ < 1 / (l : ℝ)), θ.toReal * l.cast - (1 : ℝ) < 0 := by
  intro l t tval
  rw [sub_lt_zero]
  cases l
  · norm_num
  · rw [lt_div_iff₀ ( by positivity )] at tval
    assumption
/-===============================================================-/
/- LIMITS PROOF
   ## lim n → ∞: P[X ≥ n/2] → 0                                         by: ??? -/
lemma P1_3 (l : ℕ)(θ : ℝ≥0)(ht : θ < 1 / (l : ℝ)):
  Filter.Tendsto
    (fun n : { n : ℕ // n > 0 } ↦
      (Pr_cycles_count_le_ge (pt ⟨n.1,n.2⟩ l θ ht) ⟨n.1,n.2⟩ l (⌈n/(2:ℝ)⌉.toNat)) )
  Filter.atTop (nhds 0)
  := by
  have lowerbound :
    (Filter.Tendsto (fun n : { n : ℕ // n > 0 } ↦ (0 : ℝ) ) Filter.atTop (nhds 0) ) := by
    exact tendsto_const_nhds
  have upperbound :
    (Filter.Tendsto (fun n : { n : ℕ // n > 0 } ↦ 2 * l * (n:ℝ)^( θ.toReal * l - 1 ))
      Filter.atTop (nhds 0) ) := by

    rw [← mul_zero (2 * (l : ℝ))]
    apply Filter.Tendsto.const_mul

    have comp :
      (fun k : {n : ℕ // n > 0} ↦ k.1.cast ^ (θ.toReal * l.cast - 1)) =
      (fun x : ℝ ↦ x ^ (θ.toReal * l.cast - 1)) ∘ (fun k : {n : ℕ // n > 0} ↦ k.1.cast) := by
      ext i; simp only [Function.comp_apply]
    rw [comp]
    apply Filter.Tendsto.comp (y := Filter.atTop)
    pick_goal 2; {
      have mono : Monotone (fun n : {n : ℕ // n > 0} ↦ (n.1 : ℝ) ) := by {
        intro ⟨a,a'⟩ ⟨b,b'⟩ od; simp only
        simp only [Subtype.mk_le_mk] at od
        simp only [Nat.cast_le, od]
      }
      refine Filter.tendsto_atTop_atTop_of_monotone mono ?_
      intro r; use ⟨⌈r⌉.toNat + 1,by simp only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff,
        Int.lt_toNat, CharP.cast_eq_zero, Int.ceil_pos, zero_lt_one, or_true]⟩
      simp only [Nat.cast_add, Nat.cast_one]
      rw [Int.ceil_toNat]; grw [←Nat.le_ceil r]; linarith
    }

    have bd := P1_2_bd_lt l θ ht
    rw [RCLike.neg_iff_exists_ofReal] at bd
    obtain ⟨c,⟨bd,heq⟩⟩ := bd
    rw [←heq]
    let c' := -c; have cb : c' > 0 := by exact Left.neg_pos_iff.mpr bd
    rw [show c = -c' from by exact Eq.symm (InvolutiveNeg.neg_neg c)]
    apply tendsto_rpow_neg_atTop cb

  have ne : Nonempty {n : ℕ // n > 0} := by {
    refine nonempty_subtype.mpr ?_; use 1; linarith }
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowerbound upperbound ?_ ?_
  · unfold Pr_cycles_count_le_ge; simp only
    rw [Filter.eventually_atTop]; use ⟨1,by linarith⟩
    intro b bd; exact MeasureTheory.measureReal_nonneg
  · rw [Filter.eventually_atTop]
    use ⟨1,by linarith⟩
    intro x xb
    have P2 := P1_2 l θ ht x.1 x.2; simp only at P2
    apply P2
/- EXTRACTOR
   # ∀ ε>0, ∃ n₁, P[X ≥ n₁/2] < ε                                      by:def lim? -/
lemma P1_Extractor (l : ℕ)(θ : ℝ≥0)(ht : θ < 1 / (l : ℝ)):
  ∀(eps : ℝ)(_ : eps > 0), ∃(n : ℕ)(h : n > 0),
  Pr_cycles_count_le_ge (pt ⟨n,h⟩ l θ ht) ⟨n,h⟩ l (⌈n/(2:ℝ)⌉.toNat) < eps := by
  intro eps bde
  have prev := P1_3 l θ ht
  have : Nonempty { n : ℕ // n > 0 } := by
    refine nonempty_subtype.mpr ?_; use 1; linarith
  rw [Metric.tendsto_atTop] at prev
  specialize (prev eps (by linarith))
  obtain ⟨⟨n,np⟩,prev⟩ := prev
  use n, np; specialize prev ⟨n,np⟩ (by rfl)
  simp only [dist_zero_right, norm_eq_abs] at prev
  rw [abs_of_nonneg] at prev
  pick_goal 2; { unfold Pr_cycles_count_le_ge; exact MeasureTheory.measureReal_nonneg }
  assumption
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
#check SimpleGraph.Coloring
/-===============================================================-/
/- Forall Graphs G, χ(G) * α(G) ≥ |G|
   ## χ(G') * α(G') ≥ |G'|                    by:facts and logic -/
theorem mul_χ_α_ge (n : API_𝔾.Nval):
  ∀(G : ΩK n), (ΩKtoFinGraph n G).chromaticNumber.toNat * αG G ≥ n.1 := by {
    intro G
    -- get coloring
    set G' := ((ΩKtoFinGraph n) G)
    have hc := G'.colorable_chromaticNumber_of_fintype
    set χ := (SimpleGraph.chromaticNumber G')
    rw [G'.colorable_iff_exists_bdd_nat_coloring χ.toNat] at hc
    obtain ⟨C,hc⟩ := hc

    let Cfin : SimpleGraph.Coloring G' (Fin (χ.toNat)) :=
      SimpleGraph.Coloring.mk
        ( fun v ↦ (⟨C v,hc v⟩ : Fin (χ.toNat)) )
        ( by
          simp only [SimpleGraph.completeGraph_eq_top, ne_eq, Fin.mk.injEq]
          intro a b adj
          exact SimpleGraph.Coloring.valid C adj
           )
    obtain hi := Cfin.color_classes_independent
    unfold IsAntichain Set.Pairwise at hi
    simp only [ne_eq, Pi.compl_apply, compl_iff_not] at hi

    obtain finite : Fintype Cfin.colorClasses := by exact Fintype.ofFinite ↑Cfin.colorClasses
    obtain ⟨p1,p2⟩ := Cfin.colorClasses_isPartition

    -- Have universe of vertices
    rw [show n.1 = Finset.card (Finset.univ : Finset (Fin n.1)) by simp only [Finset.card_fin]]

    -- Get Indsets
    simp only [ge_iff_le]
    unfold αG MaxIndSet

    set max := MaxIndSetP G
    generalize ch : (Classical.choose _) = Imax;
    rw [ch] at max
    unfold isMax_Indset at max
    obtain ⟨Imax,Ip⟩ := Imax
    simp_all only


    classical
    rw [Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin n.1)) )
      (t := (Cfin.colorClasses.toFinset))
      (f := fun v : Fin n.1 ↦ Cfin.colorClass (Cfin v))
      (by
        simp only [Finset.coe_univ, Set.coe_toFinset, Set.mapsTo_univ_iff]
        intro v; apply Cfin.mem_colorClasses
      )]
    grw [Finset.sum_le_sum
      ( g := fun _ ↦ Imax.toFinset.card )
      ( by
        intro CL HCL
        have : CL ∈ IndSetsG G := by
          unfold IndSetsG is_IndSetG; simp only [ne_eq, Subtype.forall, Subtype.mk.injEq,
            Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha b hb neq

          have t : CL = Cfin.colorClass (Cfin a) :=
            by
            simp only [SimpleGraph.completeGraph_eq_top]
            have : a ∈ Cfin.colorClass (Cfin a) := by exact rfl
            specialize p2 a
            obtain ⟨CL',⟨p2,p2'⟩⟩ := p2; simp only [and_imp] at p2'
            simp only [Set.mem_toFinset] at HCL
            apply p2' CL HCL at ha
            apply p2' (Cfin.colorClass (Cfin a))
              (by exact SimpleGraph.Coloring.mem_colorClasses Cfin) at this
            rw [ha, ←this]

          have : ¬G'.Adj a b := by
            rw [t] at ha hb
            specialize hi (Cfin a) ha hb neq
            assumption
          unfold G' ΩKtoFinGraph at this; simp only [ne_eq, not_and, not_forall,
            Bool.not_eq_true] at this
          specialize this neq; obtain ⟨⟩ := this
          assumption
        specialize max ⟨CL,this⟩
        simp only [Set.toFinset_card, ge_iff_le] at max
        simp only [SimpleGraph.completeGraph_eq_top, Set.toFinset_card, ge_iff_le]
        grw [←max]

        have heq : {a | Cfin.colorClass (Cfin a) = CL}.toFinset.card = CL.toFinset.card := by
          congr
          · ext x; simp only [SimpleGraph.completeGraph_eq_top]
            constructor
            · intro a; rw [←a]; exact rfl
            · intro a
              have t : CL = Cfin.colorClass (Cfin x) :=
              by
                simp only [SimpleGraph.completeGraph_eq_top]
                have : x ∈ Cfin.colorClass (Cfin x) := by exact rfl
                specialize p2 x
                obtain ⟨CL',⟨p2,p2'⟩⟩ := p2; simp only [and_imp] at p2'
                simp only [Set.mem_toFinset] at HCL
                apply p2' CL HCL at a
                apply p2' (Cfin.colorClass (Cfin x))
                  (by exact SimpleGraph.Coloring.mem_colorClasses Cfin) at this
                rw [a, ←this]
              exact t.symm
          · ext a; constructor
            · intro h; rw [←h]; exact rfl
            · intro b
              have t : CL = Cfin.colorClass (Cfin a) :=
              by
                simp only [SimpleGraph.completeGraph_eq_top]
                have : a ∈ Cfin.colorClass (Cfin a) := by exact rfl
                specialize p2 a
                obtain ⟨CL',⟨p2,p2'⟩⟩ := p2; simp only [and_imp] at p2'
                simp only [Set.mem_toFinset] at HCL
                apply p2' CL HCL at b
                apply p2' (Cfin.colorClass (Cfin a))
                  (by exact SimpleGraph.Coloring.mem_colorClasses Cfin) at this
                rw [b, ←this]
              exact t.symm

        simp only [SimpleGraph.completeGraph_eq_top, Set.toFinset_setOf, Set.toFinset_card] at heq
        rw [heq]
      )
    ]
    -- cont.
    simp only [Set.toFinset_card, Finset.sum_const, smul_eq_mul]
    rw [Nat.mul_le_mul_right_iff (by
      unfold IndSetsG is_IndSetG at Ip;
      have t := MaxIndSet_LB G; simp only [Set.toFinset_card] at t
      unfold MaxIndSet at t; rw [ch] at t; simp only [t]
    )]
    clear max

    -- OBTAIN SURJECTION.
    have surj : χ.toNat ≤ G'.chromaticNumber := by exact ENat.coe_toNat_le_self χ
    rw [SimpleGraph.le_chromaticNumber_iff_forall_surjective] at surj
    specialize surj Cfin

    conv =>
      enter [2]
      rw [show χ.toNat = Finset.card (Finset.univ : Finset (Fin (χ.toNat))) from
        by simp only [Finset.card_univ, Fintype.card_fin]]
    rw [←Finset.card_univ]
    refine Finset.card_le_card_of_surjOn
      (fun i ↦ ⟨Cfin.colorClass i, by
        unfold Function.Surjective at surj
        specialize surj i; obtain ⟨a,surj⟩ := surj; rw [←surj]
        exact SimpleGraph.Coloring.mem_colorClasses Cfin ⟩)
      (by
        intro CL mem
        simp only [Finset.coe_univ, Set.image_univ, Set.mem_range]
        unfold Function.Surjective at surj
        obtain ⟨CL,CLP⟩ := CL
        simp only [Subtype.mk.injEq]
        obtain ⟨a,amem⟩ : ∃a, a ∈ CL := by
          by_contra cnt; simp only [not_exists] at cnt;
          have empty : CL = ∅ := by exact Set.subset_eq_empty cnt rfl
          rw [empty] at CLP; contradiction
        use (⟨C a, hc a⟩); ext x
        constructor
        · intro h
          have t : a ∈ Cfin.colorClass ⟨C a,hc a⟩ := by exact rfl
          have t' : Cfin.colorClass ⟨C a,hc a⟩ = CL := by
            specialize p2 a; obtain ⟨CL',p2⟩ := p2
            simp only [and_imp] at p2
            obtain ⟨_,p2⟩:= p2
            apply p2 CL CLP at amem
            have CaMEM : Cfin.colorClass ⟨C a,hc a⟩ ∈ Cfin.colorClasses := by
              apply SimpleGraph.Coloring.mem_colorClasses
            apply p2 (Cfin.colorClass ⟨C a,hc a⟩) CaMEM at t
            rw [t, ← amem]
          rwa [←t']
        · intro h
          have t : a ∈ Cfin.colorClass ⟨C a,hc a⟩ := by exact rfl
          have t' : Cfin.colorClass ⟨C a,hc a⟩ = CL := by
            specialize p2 a; obtain ⟨CL',p2⟩ := p2
            simp only [and_imp] at p2
            obtain ⟨_,p2⟩:= p2
            apply p2 CL CLP at amem
            have CaMEM : Cfin.colorClass ⟨C a,hc a⟩ ∈ Cfin.colorClasses := by
              apply SimpleGraph.Coloring.mem_colorClasses
            apply p2 (Cfin.colorClass ⟨C a,hc a⟩) CaMEM at t
            rw [t, ← amem]
          rwa [t']
         )
  }
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

  --## let G ~ G(n, p)

  --## let X := "number of cycles in G of size ≤ l"

  -- [TODO] pass NON_ZERO probability into P2_Extractor
  have P1 := P1_Extractor l sorry sorry (1/2) (by linarith)
  obtain ⟨n1,bd1,P1⟩ := P1

  -- [TODO] pass NON_ZERO probability into P2_Extractor
  have P2 := P2_Extractor sorry sorry (1/2) (by linarith)
  obtain ⟨n2,bd2,P2⟩ := P2

  let n' := max n1 n2;

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

  #check mul_χ_α_ge
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
