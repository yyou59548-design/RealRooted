import RealRooted.FactorialCompression.Internal.Compression
import RealRooted.FactorialCompression.Internal.Multiplier
import RealRooted.EulerOperator

open Polynomial RealRooted RealRooted.FactorialCompression.Internal

noncomputable section
namespace RealRooted.FactorialCompression

/-- The exact derivative identity of final manuscript Lemma 3.1. -/
theorem h_previous_derivative (r : ℕ) (hr : 1 ≤ r) :
    h (r - 1) = h r - C (2 / (r : ℝ)) * (X * (h r).derivative) := by
  cases r with
  | zero => lia
  | succ r =>
      rw [show r + 1 - 1 = r by lia]
      ext k
      rw [coeff_sub, coeff_C_mul]
      change (h r).coeff k = (h (r + 1)).coeff k -
        (2 / ((r + 1 : ℕ) : ℝ)) * (theta (h (r + 1))).coeff k
      rw [coeff_theta]
      have hlower := h_coeff_lower r k
      have hrne : (r : ℝ) + 1 ≠ 0 := by positivity
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
      nlinarith [hlower]

/-- The finite diagonal multiplier commutes with the Euler operator,
without any degree or root assumption. -/
theorem finiteMultiplier_theta (N : ℕ) (p f : ℝ[X]) :
    finiteMultiplier N p (theta f) = theta (finiteMultiplier N p f) := by
  ext k
  simp only [RealRooted.FactorialCompression.Internal.coeff_finiteMultiplier, coeff_theta]
  split_ifs <;> ring

/-- The exact filtered derivative identity used at roots of the common image. -/
theorem filtered_h_previous_derivative (N : ℕ) (p : ℝ[X]) (r : ℕ) (hr : 1 ≤ r) :
    finiteMultiplier N p (h (r - 1)) =
      finiteMultiplier N p (h r) -
        C (2 / (r : ℝ)) * (X * (finiteMultiplier N p (h r)).derivative) := by
  rw [h_previous_derivative r hr]
  have hpencil : h r - C (2 / (r : ℝ)) * (X * (h r).derivative) =
      C 1 * h r + C (-(2 / (r : ℝ))) * theta (h r) := by
    simp [theta]
    ring
  rw [hpencil, finiteMultiplier_pencil, finiteMultiplier_theta]
  simp [theta]
  ring

end RealRooted.FactorialCompression

