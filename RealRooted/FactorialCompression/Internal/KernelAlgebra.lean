import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-
Universal scalar and coefficient algebra from the authoritative manuscript.
This file contains proofs, not placeholders for the manuscript theorems.
This file contains the scalar algebra used by the factorial-compression proof.
-/

namespace RealRooted.FactorialCompression.Internal

/-- The scalar inequality used in manuscript equation (4.10).
The denominator need not be positive; both ratio signs are explicit. -/
theorem key_sign {r u v w : ℝ} (hr : r < 0)
    (hv : 0 < v / u) (hw : w / u < 0) :
    (w + r * v) / u < 0 := by
  rw [add_div, mul_div_assoc]
  exact add_neg hw (mul_neg_of_neg_of_pos hr hv)

/-- The coefficient bracket identity in the proof of Lemma 4.2.
This proves only its ring algebra, not the polynomial operator identities. -/
theorem kernel_coefficient_bracket (N k : ℝ) :
    (3 / 4 : ℝ) * (N + 1) * (N + 2 - 2 * k) + N * k -
        (1 / 4 : ℝ) * (N + 2 - 2 * k) * (N + 1 - 2 * k) =
      (k + (N + 2) / 2) * (N + 1 - k) := by
  ring

end RealRooted.FactorialCompression.Internal

