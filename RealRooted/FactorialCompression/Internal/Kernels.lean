import RealRooted.FactorialCompression.Internal.Compression
import RealRooted.FactorialCompression.Internal.RootSignRatios
import RealRooted.Basic.Coefficients

/-!
# The exact kernels in manuscript Lemma 4.3

The finite-sum definition of `h` is unchanged.  Its recurrence is obtained
coefficientwise, and its root geometry is proved for every natural index by
the manuscript's sign argument.  The constant/linear first pair is explicit.
-/

open Polynomial RealRooted

noncomputable section

namespace RealRooted.FactorialCompression.Internal

@[simp] theorem h_coeff_zero (r : ℕ) : (h r).coeff 0 = 1 := by
  rw [coeff_h]
  simp only [mul_zero, Nat.zero_le, if_true, Nat.factorial_zero, Nat.cast_one,
    one_mul, Nat.sub_zero]
  exact div_self (by positivity)

theorem h_coeff_pos (r k : ℕ) (hk : 2 * k ≤ r) : 0 < (h r).coeff k := by
  rw [coeff_h, if_pos hk]
  positivity

theorem h_nonneg (r : ℕ) : HasNonnegCoeffs (h r) := by
  intro k
  rw [coeff_h]
  split <;> positivity

theorem h_ne_zero (r : ℕ) : h r ≠ 0 := by
  intro heq
  have hz := h_coeff_zero r
  simp [heq] at hz

theorem h_pos_leading (r : ℕ) : 0 < (h r).leadingCoeff :=
  (h_nonneg r).pos_leadingCoeff (h_ne_zero r)

theorem h_natDegree (r : ℕ) : (h r).natDegree = r / 2 := by
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_h, if_neg (by lia)]
  · apply le_natDegree_of_ne_zero
    exact ne_of_gt (h_coeff_pos r (r / 2) (by lia))

@[simp] theorem h_one : h 1 = 1 := by
  ext k
  cases k with
  | zero => simp
  | succ k => simp [coeff_h, coeff_one, show ¬ 2 * (k + 1) ≤ 1 by lia]

theorem h_two_factor : h 2 = C (2 : ℝ) * (X - C (-1 / 2 : ℝ)) := by
  ext k
  cases k with
  | zero => norm_num [coeff_h]
  | succ k =>
      cases k with
      | zero => norm_num [coeff_h]
      | succ k => simp [coeff_h, coeff_X, show ¬ 2 * (k + 1 + 1) ≤ 2 by lia,
          show k + 1 + 1 ≠ 1 by lia]

theorem h_two_roots : (h 2).roots = {-1 / 2} := by
  rw [h_two_factor, roots_C_mul _ (by norm_num), roots_X_sub_C]

private theorem factorial_real_pred (r : ℕ) (hr : 1 ≤ r) :
    (Nat.factorial r : ℝ) = (r : ℝ) * (Nat.factorial (r - 1) : ℝ) := by
  have heq : r = (r - 1) + 1 := by lia
  conv_lhs => rw [heq, Nat.factorial_succ]
  push_cast
  congr 1
  exact_mod_cast (show (r - 1) + 1 = r by lia)

private theorem h_recurrence_coeff_succ (r k : ℕ) (hr : 1 ≤ r) :
    (h (r + 1)).coeff (k + 1) = (h r).coeff (k + 1) +
      (2 * (r : ℝ)) * (h (r - 1)).coeff k := by
  by_cases hguard : 2 * (k + 1) ≤ r + 1
  · have hprev : 2 * k ≤ r - 1 := by lia
    by_cases hmid : 2 * (k + 1) ≤ r
    · have hd : r + 1 - 2 * (k + 1) = (r - 2 * (k + 1)) + 1 := by lia
      have he : r - 1 - 2 * k = (r - 2 * (k + 1)) + 1 := by lia
      have hrreal : (r : ℝ) = ((r - 2 * (k + 1) : ℕ) : ℝ) + 2 * (k : ℝ) + 2 := by
        exact_mod_cast (show r = (r - 2 * (k + 1)) + 2 * k + 2 by lia)
      rw [coeff_h, if_pos hguard, coeff_h, if_pos hmid, coeff_h, if_pos hprev,
        hd, he]
      simp only [Nat.factorial_succ]
      push_cast
      simp only [factorial_real_pred r hr, hrreal]
      have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hdfac : (Nat.factorial (r - 2 * (k + 1)) : ℝ) ≠ 0 := by positivity
      have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
      have hdpos : ((r - 2 * (k + 1) : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · have hbound : 2 * (k + 1) = r + 1 := by lia
      have hd : r + 1 - 2 * (k + 1) = 0 := by lia
      have he : r - 1 - 2 * k = 0 := by lia
      have hrreal : (r : ℝ) = 2 * (k : ℝ) + 1 := by
        exact_mod_cast (show r = 2 * k + 1 by lia)
      rw [coeff_h, if_pos hguard, coeff_h, if_neg hmid, coeff_h, if_pos hprev,
        hd, he, Nat.factorial_zero]
      simp only [Nat.factorial_succ]
      push_cast
      simp only [factorial_real_pred r hr, hrreal]
      have hkfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  · have hmid : ¬ 2 * (k + 1) ≤ r := by lia
    have hprev : ¬ 2 * k ≤ r - 1 := by lia
    simp [coeff_h, hguard, hmid, hprev]

/-- Closed-coefficient derivation of manuscript equation (4.4). -/
theorem h_recurrence (r : ℕ) (hr : 1 ≤ r) :
    h (r + 1) = h r + C (2 * (r : ℝ)) * X * h (r - 1) := by
  ext k
  cases k with
  | zero => simp [mul_assoc]
  | succ k =>
      simpa [mul_assoc] using h_recurrence_coeff_succ r k hr

private theorem h_base_geometry :
    SimpleNegativeRoots (h 2) ∧ ManuscriptStrictInterl (h 1) (h 2) := by
  have hsimple : SimpleNegativeRoots (h 2) := by
    refine ⟨h_ne_zero 2, Splits.of_natDegree_eq_one (by simpa using h_natDegree 2), ?_, ?_⟩
    · simp [h_two_roots]
    · intro r hr
      simp only [h_two_roots, Multiset.mem_singleton] at hr
      subst r
      norm_num
  refine ⟨hsimple, h_pos_leading 1, h_pos_leading 2, ?_, hsimple.2.1,
    [], [-1 / 2], by simp, by simp, ?_, ?_, Or.inl ⟨by simp, True.intro⟩⟩
  · simp
  · simp
  · simp [h_two_roots]

private theorem h_geometry (r : ℕ) (hr : 1 ≤ r) :
    SimpleNegativeRoots (h (r + 1)) ∧ ManuscriptStrictInterl (h r) (h (r + 1)) := by
  induction r, hr using Nat.le_induction with
  | base => exact h_base_geometry
  | succ r hr ih =>
      apply root_sign_criterion ih.1 (h_pos_leading (r + 1))
        (by rw [h_natDegree]; lia) (h_nonneg (r + 2))
        (by rw [h_coeff_zero]; norm_num) (h_pos_leading (r + 2))
        (by rw [h_natDegree, h_natDegree]; lia)
      intro s hs
      have hsneg : s < 0 := ih.1.2.2.2 s ((mem_roots ih.1.1).mpr hs)
      have hratio : 0 < (h r).eval s / (h (r + 1)).derivative.eval s :=
        ih.2.root_right_sign hs
      have heval : (h (r + 2)).eval s =
          2 * ((r + 1 : ℕ) : ℝ) * s * (h r).eval s := by
        rw [show r + 2 = (r + 1) + 1 by lia, h_recurrence (r + 1) (by lia)]
        simp [hs.eq_zero, show r + 1 - 1 = r by lia]
      rw [heval, mul_div_assoc]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by positivity) hsneg) hratio

/-- All simple-negative kernel roots, without a finite-index bound. -/
theorem h_simple_negative (r : ℕ) (hr : 2 ≤ r) : SimpleNegativeRoots (h r) := by
  simpa [show r - 1 + 1 = r by lia] using (h_geometry (r - 1) (by lia)).1

/-- Includes the manuscript's explicit constant/linear first pair. -/
theorem h_strict_interl (r : ℕ) (hr : 1 ≤ r) :
    ManuscriptStrictInterl (h r) (h (r + 1)) := (h_geometry r hr).2

/-- Positive decomposition of manuscript equation (4.9). -/
theorem kernel_positive_identity (N : ℕ) (hN : 1 ≤ N) :
    kernel N = C (1 / 2 : ℝ) * h (N + 1) +
      C ((N : ℝ) / 2) * X * h (N - 1) + C (N : ℝ) * X * h N := by
  unfold kernel
  simp only [h_recurrence N hN]
  ext k
  simp only [sub_mul, mul_assoc, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul]
  ring

theorem kernel_nonneg (N : ℕ) (hN : 1 ≤ N) : HasNonnegCoeffs (kernel N) := by
  rw [kernel_positive_identity N hN]
  have hfirst : HasNonnegCoeffs (C (1 / 2 : ℝ) * h (N + 1)) :=
    (hasNonnegCoeffs_C (by norm_num)).mul (h_nonneg (N + 1))
  have hsecond : HasNonnegCoeffs (C ((N : ℝ) / 2) * X * h (N - 1)) :=
    ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X).mul (h_nonneg (N - 1))
  have hthird : HasNonnegCoeffs (C (N : ℝ) * X * h N) :=
    ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X).mul (h_nonneg N)
  exact (hfirst.add hsecond).add hthird

@[simp] theorem kernel_coeff_zero (N : ℕ) : (kernel N).coeff 0 = 1 / 2 := by
  norm_num [kernel, sub_mul, mul_assoc]

private theorem kernel_coeff_succ (N k : ℕ) (hN : 1 ≤ N) :
    (kernel N).coeff (k + 1) =
      (1 / 2 : ℝ) * (h (N + 1)).coeff (k + 1) +
      ((N : ℝ) / 2) * (h (N - 1)).coeff k + (N : ℝ) * (h N).coeff k := by
  simp [kernel_positive_identity N hN, mul_assoc]

/-- Strict positivity of every coefficient through the manuscript degree. -/
theorem kernel_coeff_pos (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ (N + 2) / 2) :
    0 < (kernel N).coeff k := by
  cases k with
  | zero => rw [kernel_coeff_zero]; norm_num
  | succ k =>
      rw [kernel_coeff_succ N k hN]
      have hlast : 0 < (N : ℝ) * (h N).coeff k :=
        mul_pos (by exact_mod_cast (show 0 < N by lia)) (h_coeff_pos N k (by lia))
      have hfirst : 0 ≤ (1 / 2 : ℝ) * (h (N + 1)).coeff (k + 1) :=
        mul_nonneg (by norm_num) (h_nonneg (N + 1) _)
      have hsecond : 0 ≤ ((N : ℝ) / 2) * (h (N - 1)).coeff k :=
        mul_nonneg (by positivity) (h_nonneg (N - 1) _)
      linarith

theorem kernel_ne_zero (N : ℕ) : kernel N ≠ 0 := by
  intro hzero
  have hz := kernel_coeff_zero N
  norm_num [hzero] at hz

theorem kernel_pos_leading (N : ℕ) (hN : 1 ≤ N) : 0 < (kernel N).leadingCoeff :=
  (kernel_nonneg N hN).pos_leadingCoeff (kernel_ne_zero N)

theorem kernel_natDegree (N : ℕ) (hN : 1 ≤ N) :
    (kernel N).natDegree = (N + 2) / 2 := by
  have hhalf : (N + 2) / 2 = N / 2 + 1 := by lia
  rw [hhalf]
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    cases k with
    | zero => lia
    | succ k =>
        rw [kernel_coeff_succ N k hN]
        simp [coeff_h, show ¬ 2 * (k + 1) ≤ N + 1 by lia,
          show ¬ 2 * k ≤ N - 1 by lia, show ¬ 2 * k ≤ N by lia]
  · apply le_natDegree_of_ne_zero
    exact ne_of_gt (kernel_coeff_pos N (N / 2 + 1) hN (by lia))

private theorem kernel_geometry (N : ℕ) (hN : 1 ≤ N) :
    SimpleNegativeRoots (kernel N) ∧ ManuscriptStrictInterl (h (N + 1)) (kernel N) := by
  have hf := h_simple_negative (N + 1) (by lia)
  apply root_sign_criterion hf (h_pos_leading (N + 1))
    (by rw [h_natDegree]; lia) (kernel_nonneg N hN)
    (by rw [kernel_coeff_zero]; norm_num) (kernel_pos_leading N hN)
    (by rw [kernel_natDegree N hN, h_natDegree]; lia)
  intro s hs
  have hsneg : s < 0 := hf.2.2.2 s ((mem_roots hf.1).mpr hs)
  have hratio : 0 < (h N).eval s / (h (N + 1)).derivative.eval s :=
    (h_strict_interl N hN).root_right_sign hs
  have heval : (kernel N).eval s = ((N : ℝ) * s - 1 / 4) * (h N).eval s := by
    simp [kernel, hs.eq_zero]
  rw [heval, mul_div_assoc]
  have hNs : (N : ℝ) * s < 0 := mul_neg_of_pos_of_neg (by positivity) hsneg
  exact mul_neg_of_neg_of_pos (by linarith) hratio

theorem kernel_simple_negative (N : ℕ) (hN : 1 ≤ N) :
    SimpleNegativeRoots (kernel N) := (kernel_geometry N hN).1

theorem h_strict_interl_kernel (N : ℕ) (hN : 1 ≤ N) :
    ManuscriptStrictInterl (h (N + 1)) (kernel N) := (kernel_geometry N hN).2

end RealRooted.FactorialCompression.Internal
