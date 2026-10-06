import RealRooted.FactorialCompression.Internal.Definitions
import RealRooted.FactorialCompression.Internal.KernelAlgebra
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.FactorialCompression.Internal

private theorem coeff_finiteMultiplier (N k : ℕ) (p f : ℝ[X]) :
    (finiteMultiplier N p f).coeff k =
      if k ≤ N then p.coeff k * f.coeff k / (Nat.choose N k : ℝ) else 0 := by
  classical
  unfold finiteMultiplier
  simp_rw [C_mul_X_pow_eq_monomial]
  rw [finsetSum_coeff]
  by_cases hk : k ≤ N
  · simp [coeff_monomial, hk, div_mul_eq_mul_div]
  · simp [coeff_monomial, Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.lt_of_not_le hk)), hk]

theorem coeff_compression (N k : ℕ) (p : ℝ[X]) :
    (compression N p).coeff k =
      if k ≤ N then mu N k * p.coeff k else 0 := by
  classical
  unfold compression
  simp_rw [C_mul_X_pow_eq_monomial]
  rw [finsetSum_coeff]
  by_cases hk : k ≤ N
  · simp [coeff_monomial, hk]
  · simp [coeff_monomial, Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.lt_of_not_le hk)), hk]

theorem coeff_h (r k : ℕ) :
    (h r).coeff k = if 2 * k ≤ r then
      (Nat.factorial r : ℝ) /
        ((Nat.factorial k : ℝ) * (Nat.factorial (r - 2 * k) : ℝ)) else 0 := by
  classical
  have hi : k ≤ r / 2 ↔ 2 * k ≤ r := by lia
  simp [h, finsetSum_coeff, coeff_C_mul, coeff_X_pow, Nat.lt_succ_iff, hi]

/-- Exact normalization in manuscript (4.6), including zero coefficients
outside the supported half-degree range. -/
theorem choose_mul_mu (N k : ℕ) (hk : k ≤ N) :
    (Nat.choose N k : ℝ) * mu N k = (1 / ((N : ℝ) + 1)) * (h (N + 1)).coeff k := by
  by_cases hguard : 2 * k ≤ N + 1
  · have hfac : (Nat.choose N k : ℝ) * (Nat.factorial k : ℝ) *
        (Nat.factorial (N - k) : ℝ) = (Nat.factorial N : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hden : (Nat.factorial (N + 1 - 2 * k) : ℝ) ≠ 0 := by positivity
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    rw [mu, if_pos hguard, coeff_h, if_pos hguard, Nat.factorial_succ]
    push_cast
    field_simp
    nlinarith [hfac]
  · simp [mu, coeff_h, hguard]

/-- First exact operator identity of manuscript Lemma 4.2. -/
theorem compression_common_kernel (N : ℕ) (p : ℝ[X]) :
    compression N p = C (1 / ((N : ℝ) + 1)) * finiteMultiplier N p (h (N + 1)) := by
  ext k
  rw [coeff_compression, coeff_C_mul, coeff_finiteMultiplier]
  by_cases hk : k ≤ N
  · rw [if_pos hk, if_pos hk]
    have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hmu : mu N k =
        ((1 / ((N : ℝ) + 1)) * (h (N + 1)).coeff k) / (Nat.choose N k : ℝ) := by
      apply (eq_div_iff hchoose).mpr
      simpa [mul_comm] using choose_mul_mu N k hk
    rw [hmu]
    ring
  · simp [hk]

/-- Normalization for the shifted term in manuscript (4.7). -/
theorem choose_mul_mu_shift (N k : ℕ) (hk : k ≤ N) :
    (Nat.choose N k : ℝ) * mu (N + 1) (k + 1) = (h N).coeff k := by
  have hguard : 2 * (k + 1) ≤ N + 1 + 1 ↔ 2 * k ≤ N := by lia
  by_cases hsupport : 2 * k ≤ N
  · have hfac : (Nat.choose N k : ℝ) * (Nat.factorial k : ℝ) *
        (Nat.factorial (N - k) : ℝ) = (Nat.factorial N : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hden : (Nat.factorial (N - 2 * k) : ℝ) ≠ 0 := by positivity
    have hindex : N + 1 - (k + 1) = N - k := by lia
    have hindex2 : N + 1 + 1 - 2 * (k + 1) = N - 2 * k := by lia
    rw [mu, if_pos (hguard.mpr hsupport), hindex, hindex2,
      coeff_h, if_pos hsupport]
    field_simp
    nlinarith [hfac]
  · simp [mu, coeff_h, hguard, hsupport]

theorem compression_X_mul (N : ℕ) (p : ℝ[X]) :
    compression (N + 1) (X * p) = X * finiteMultiplier N p (h N) := by
  ext k
  cases k with
  | zero => simp [coeff_compression]
  | succ k =>
      rw [coeff_compression, coeff_X_mul, coeff_X_mul, coeff_finiteMultiplier]
      have hbound : k + 1 ≤ N + 1 ↔ k ≤ N := by lia
      by_cases hk : k ≤ N
      · rw [if_pos (hbound.mpr hk), if_pos hk]
        have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos hk).ne'
        have hmu : mu (N + 1) (k + 1) = (h N).coeff k / (Nat.choose N k : ℝ) := by
          apply (eq_div_iff hchoose).mpr
          simpa [mul_comm] using choose_mul_mu_shift N k hk
        rw [hmu]
        ring
      · simp [hbound, hk]

/-- A coefficient lowering identity with the zero boundary included. -/
theorem h_coeff_lower (r k : ℕ) :
    ((r : ℝ) + 1 - 2 * (k : ℝ)) * (h (r + 1)).coeff k =
      ((r : ℝ) + 1) * (h r).coeff k := by
  by_cases hk : 2 * k ≤ r
  · have hk' : 2 * k ≤ r + 1 := by lia
    have hi : r + 1 - 2 * k = (r - 2 * k) + 1 := by lia
    have hc : ((r - 2 * k : ℕ) : ℝ) + 1 = (r : ℝ) + 1 - 2 * (k : ℝ) := by
      have he : r = (r - 2 * k) + 2 * k := by lia
      have heq := congrArg (fun n : ℕ => (n : ℝ)) he
      push_cast at heq
      linarith
    rw [coeff_h, if_pos hk', coeff_h, if_pos hk, hi]
    simp only [Nat.factorial_succ]
    push_cast
    rw [hc]
    have hd : (Nat.factorial (r - 2 * k) : ℝ) ≠ 0 := by positivity
    have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have ha : (r : ℝ) + 1 - 2 * (k : ℝ) ≠ 0 := by
      rw [← hc]
      positivity
    field_simp
  · by_cases hk' : 2 * k ≤ r + 1
    · have he : 2 * k = r + 1 := by lia
      have hc : (r : ℝ) + 1 - 2 * (k : ℝ) = 0 := by
        have := congrArg (fun n : ℕ => (n : ℝ)) he
        push_cast at this
        linarith
      simp [coeff_h, hk, hk', hc]
    · simp [coeff_h, hk, hk']

theorem h_coeff_shift (r k : ℕ) :
    ((k : ℝ) + 1) * (h (r + 2)).coeff (k + 1) =
      ((r : ℝ) + 2) * ((r : ℝ) + 1) * (h r).coeff k := by
  have hi : 2 * (k + 1) ≤ r + 2 ↔ 2 * k ≤ r := by lia
  by_cases hk : 2 * k ≤ r
  · have hd : r + 2 - 2 * (k + 1) = r - 2 * k := by lia
    rw [coeff_h, if_pos (hi.mpr hk), coeff_h, if_pos hk, hd]
    simp only [show r + 2 = (r + 1) + 1 by lia, Nat.factorial_succ]
    push_cast
    have hdne : (Nat.factorial (r - 2 * k) : ℝ) ≠ 0 := by positivity
    have hkne : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    have hkn : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · simp [coeff_h, hk, hi]

theorem choose_mul_mu_next (N k : ℕ) (hk : k ≤ N) :
    (((N : ℝ) + 2) * ((N : ℝ) + 1)) *
        ((Nat.choose N k : ℝ) * mu (N + 1) k) =
      ((N : ℝ) + 1 - (k : ℝ)) * (h (N + 2)).coeff k := by
  by_cases hs : 2 * k ≤ N + 2
  · have hfac : (Nat.choose N k : ℝ) * (Nat.factorial k : ℝ) *
        (Nat.factorial (N - k) : ℝ) = (Nat.factorial N : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    have hi : N + 1 - k = (N - k) + 1 := by lia
    have hc : ((N - k : ℕ) : ℝ) + 1 = (N : ℝ) + 1 - (k : ℝ) := by
      have he : N = (N - k) + k := by lia
      have := congrArg (fun n : ℕ => (n : ℝ)) he
      push_cast at this
      linarith
    rw [mu, if_pos (by simpa [Nat.add_assoc] using hs), coeff_h, if_pos hs, hi]
    simp only [show N + 2 = (N + 1) + 1 by lia, Nat.factorial_succ]
    push_cast
    rw [hc]
    have hd : (Nat.factorial (N + 2 - 2 * k) : ℝ) ≠ 0 := by positivity
    have hkd : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    field_simp
    linear_combination (((N : ℝ) + 2) * ((N : ℝ) + 1 - (k : ℝ))) * hfac
  · simp [mu, coeff_h, show ¬ 2 * k ≤ N + 1 + 1 by simpa [Nat.add_assoc] using hs, hs]

/-- Manuscript (4.8), including the absent endpoint coefficients. -/
theorem coeff_kernel_multiplier (N k : ℕ) (hk : k ≤ N) :
    (kernel N).coeff k = (Nat.choose N k : ℝ) *
      ((k : ℝ) + ((N : ℝ) + 2) / 2) * mu (N + 1) k := by
  have hD : ((N : ℝ) + 2) * ((N : ℝ) + 1) ≠ 0 := by positivity
  have hs1 := h_coeff_lower (N + 1) k
  have hs0 := h_coeff_lower N k
  have hm := choose_mul_mu_next N k hk
  have hC : (((N : ℝ) + 2) * ((N : ℝ) + 1)) * (kernel N).coeff k =
      ((k : ℝ) + ((N : ℝ) + 2) / 2) *
      ((N : ℝ) + 1 - (k : ℝ)) * (h (N + 2)).coeff k := by
    cases k with
    | zero =>
        have hz (r : ℕ) : (h r).coeff 0 = 1 := by
          rw [coeff_h]
          simp [Nat.factorial_ne_zero]
        simp [kernel, sub_mul, hz]
        ring
    | succ k =>
        have hshift := h_coeff_shift N k
        have hb := kernel_coefficient_bracket (N : ℝ) ((k : ℝ) + 1)
        simp only [kernel, sub_mul, mul_assoc, coeff_add, coeff_sub, coeff_C_mul,
          coeff_X_mul] at *
        push_cast at *
        linear_combination
          -(3 / 4 : ℝ) * ((N : ℝ) + 1) * hs1 +
          (1 / 4 : ℝ) * (((N : ℝ) + 2) * hs0 +
            ((N : ℝ) + 1 - 2 * ((k : ℝ) + 1)) * hs1) +
          -(N : ℝ) * hshift + (h (N + 2)).coeff (k + 1) * hb
  apply mul_left_cancel₀ hD
  rw [hC]
  linear_combination -((k : ℝ) + ((N : ℝ) + 2) / 2) * hm

/-- The second exact operator identity in manuscript Lemma 4.2. -/
theorem compression_nextPolynomial (N : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ N) :
    compression (N + 1) (nextPolynomial N p) =
      finiteMultiplier N p (kernel N) + X * finiteMultiplier N p (h N) := by
  have hshift := compression_X_mul N p
  ext k
  have htheta : (nextPolynomial N p).coeff k =
      (X * p).coeff k + ((k : ℝ) + ((N : ℝ) + 2) / 2) * p.coeff k := by
    cases k with
    | zero => simp [nextPolynomial, add_mul]
    | succ k =>
        simp [nextPolynomial, add_mul, coeff_derivative]
        ring
  rw [coeff_compression, htheta, coeff_add, coeff_finiteMultiplier,
    ← congrArg (fun q : ℝ[X] => q.coeff k) hshift, coeff_compression]
  by_cases hk : k ≤ N
  · have hk1 : k ≤ N + 1 := by lia
    simp only [ite_eq_left hk1, ite_eq_left hk]
    have hchoose : (Nat.choose N k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    rw [coeff_kernel_multiplier N k hk]
    field_simp
    ring
  · have hpk : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (lt_of_not_ge hk))
    simp [hk, hpk]

end RealRooted.FactorialCompression.Internal
