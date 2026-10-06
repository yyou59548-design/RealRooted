import RealRooted.FactorialCompression.Internal.RootSigns
import RealRooted.Interlacing.OuterDifference

/-!
# Manuscript equation (2.1)

The exact strict quotient signs follow from the independently proved
manuscript/upstream bridge and the explicit exclusion of common roots.
-/

open Polynomial

noncomputable section

namespace RealRooted.FactorialCompression.Internal

/-- Equation (2.1), at a root of the left polynomial. -/
theorem ManuscriptStrictInterl.root_left_sign {f g : ℝ[X]}
    (h : ManuscriptStrictInterl f g) {r : ℝ} (hr : f.IsRoot r) :
    g.eval r / f.derivative.eval r < 0 := by
  have hp := h.to_upstream.eval_mul_derivative_neg_of_left_root_of_no_common
    h.1 h.2.1 h.no_common_root hr
  exact (div_neg_iff).mpr (mul_neg_iff.mp hp)

/-- Equation (2.1), at a root of the right polynomial. -/
theorem ManuscriptStrictInterl.root_right_sign {f g : ℝ[X]}
    (h : ManuscriptStrictInterl f g) {s : ℝ} (hs : g.IsRoot s) :
    0 < f.eval s / g.derivative.eval s := by
  have hp := h.to_upstream.eval_mul_derivative_pos_of_right_root_of_no_common
    h.1 h.2.1 h.no_common_root hs
  exact (div_pos_iff).mpr (mul_pos_iff.mp hp)

end RealRooted.FactorialCompression.Internal
