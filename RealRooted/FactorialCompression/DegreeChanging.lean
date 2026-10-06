import RealRooted.FactorialCompression.Boundary
import RealRooted.FactorialCompression.KernelGeometry
import RealRooted.FactorialCompression.KernelIdentities

/-! The full authoritative manuscript Theorem 1.1. All levels and every
positive real a are quantified, and repeated input roots are permitted. -/

open Polynomial RealRooted RealRooted.FactorialCompression.Internal
noncomputable section
namespace RealRooted.FactorialCompression

/-- Factorial compression, for arbitrary N >= 1, 0 <= ell <= N and a > 0.
Splits makes "all zeros negative" refer to all N roots, not merely the
possibly empty list of real roots. No simplicity assumption is imposed on p. -/
theorem factorial_compression {N ell : ℕ} {a : ℝ} {p : ℝ[X]}
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a)
    (hpdegree : p.natDegree = N) (hpsplit : p.Splits)
    (hppos : 0 < p.leadingCoeff) (hproots : ∀ r ∈ p.roots, r < 0) :
    (compression N ell p).natDegree = (N + ell) / 2 ∧
    (compression (N + 1) ell (nextPolynomial a p)).natDegree = (N + ell + 1) / 2 ∧
    SimpleNegativeRoots (compression N ell p) ∧
    SimpleNegativeRoots (compression (N + 1) ell (nextPolynomial a p)) ∧
    ManuscriptStrictInterl (compression N ell p)
      (compression (N + 1) ell (nextPolynomial a p)) := by
  by_cases hmone : N + ell = 1
  · have hN1 : N = 1 := by lia
    have hell0 : ell = 0 := by lia
    have hb := factorial_compression_boundary ha
      (by simpa only [hN1] using hpdegree) hpsplit hppos hproots
    simpa [hN1, hell0] using hb
  have hm : 2 ≤ N + ell := by lia
  let U := finiteMultiplier N p (h (N + ell))
  let V := finiteMultiplier N p (h (N + ell - 1))
  let W := finiteMultiplier N p (kernel N ell a)
  have hUbound : (h (N + ell)).natDegree ≤ N := by rw [h_natDegree]; lia
  have hWbound : (kernel N ell a).natDegree ≤ N := by
    rw [kernel_natDegree N ell a hN hell ha]
    lia
  have hU : SimpleNegativeRoots U := finiteMultiplier_simpleNegativeRoots
    hpdegree hpsplit hppos hproots hUbound (h_simple_negative _ hm) (h_pos_leading _)
  have hW : SimpleNegativeRoots W := finiteMultiplier_simpleNegativeRoots
    hpdegree hpsplit hppos hproots hWbound
    (kernel_simple_negative N ell a hN hell ha hm)
    (kernel_pos_leading N ell a hN hell ha)
  have hUW : ManuscriptStrictInterl U W := finiteMultiplier_preserves_strictInterl
    hN hpdegree hpsplit hppos hproots hUbound hWbound
    (h_strict_interl_kernel N ell a hN hell ha hm)
    (h_simple_negative _ hm).2.2.2
    (kernel_simple_negative N ell a hN hell ha hm).2.2.2
  have hUd : U.natDegree = (N + ell) / 2 := by
    rw [finiteMultiplier_natDegree hpdegree hpsplit hppos hproots hUbound
      (h_ne_zero _), h_natDegree]
  have hWd : W.natDegree = (N + ell + 1) / 2 := by
    rw [finiteMultiplier_natDegree hpdegree hpsplit hppos hproots hWbound
      (kernel_ne_zero N ell a hN hell ha), kernel_natDegree N ell a hN hell ha]
  have hVd : V.natDegree = (N + ell - 1) / 2 := by
    rw [finiteMultiplier_natDegree hpdegree hpsplit hppos hproots
      (by rw [h_natDegree]; lia) (h_ne_zero _), h_natDegree]
  have hVnonneg : HasNonnegCoeffs V := by
    intro k
    dsimp [V]
    rw [coeff_finiteMultiplier]
    split_ifs with hk
    · exact div_nonneg (mul_nonneg
        ((isPFPolynomial_of_negativeRoots hpsplit hppos hproots).hasNonnegCoeffs k)
        (h_nonneg _ k)) (by positivity)
    · exact le_rfl
  have hWnonneg : HasNonnegCoeffs W :=
    (isPFPolynomial_of_negativeRoots hW.2.1 hUW.2.1 hW.2.2.2).hasNonnegCoeffs
  have hGnonneg : HasNonnegCoeffs (W + X * V) :=
    hWnonneg.add (hasNonnegCoeffs_X.mul hVnonneg)
  have hGzero : 0 < (W + X * V).coeff 0 := by
    simpa [W] using finiteMultiplier_coeff_zero_pos
      (coeff_zero_pos_of_negativeRoots hpsplit hppos hproots)
      (kernel_coeff_pos N ell a 0 hN hell ha (by lia))
  have hGd : (W + X * V).natDegree = (N + ell + 1) / 2 := by
    apply Nat.le_antisymm
    · apply (natDegree_add_le W (X * V)).trans
      apply max_le hWd.le
      have hv : (X * V).natDegree ≤ (X : ℝ[X]).natDegree + V.natDegree :=
        natDegree_mul_le
      rw [natDegree_X, hVd] at hv
      lia
    · apply le_natDegree_of_ne_zero
      apply ne_of_gt
      have hwc : 0 < W.coeff ((N + ell + 1) / 2) := by
        rw [← hWd, coeff_natDegree]
        exact hUW.2.1
      exact lt_of_lt_of_le hwc (by
        rw [coeff_add]
        exact le_add_of_nonneg_right ((hasNonnegCoeffs_X.mul hVnonneg) _))
  have hGpos : 0 < (W + X * V).leadingCoeff :=
    hGnonneg.pos_leadingCoeff (by
      intro hz
      simp [hz] at hGzero)
  have hVidentity : V = U - C (2 / ((N + ell : ℕ) : ℝ)) * (X * U.derivative) :=
    filtered_h_previous_derivative N p (N + ell) (by lia)
  have hresult : SimpleNegativeRoots (W + X * V) ∧
      ManuscriptStrictInterl U (W + X * V) := by
    apply root_sign_criterion hU hUW.1 (by rw [hUd]; lia)
      hGnonneg hGzero hGpos (by rw [hGd, hUd]; lia)
    intro r hr
    have hrneg : r < 0 := hU.2.2.2 r ((mem_roots hU.1).mpr hr)
    have hder : U.derivative.eval r ≠ 0 := hU.hasSimpleRoots.eval_derivative_ne_zero hr
    have heval : V.eval r = -(2 / ((N + ell : ℕ) : ℝ)) * r * U.derivative.eval r := by
      rw [hVidentity]
      simp [hr.eq_zero]
      ring
    have hratio : 0 < V.eval r / U.derivative.eval r := by
      rw [heval, mul_div_cancel_right₀ _ hder]
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (by positivity)) hrneg
    simpa using key_sign hrneg hratio (hUW.root_left_sign hr)
  have hscale1 : 0 < (Nat.factorial N : ℝ) / (Nat.factorial (N + ell) : ℝ) := by
    positivity
  have hscale2 : 0 < (Nat.factorial N : ℝ) / (Nat.factorial (N + ell - 1) : ℝ) := by
    positivity
  rw [compression_common_kernel, compression_nextPolynomial N ell a p hN hpdegree.le]
  refine ⟨?_, ?_, hU.C_mul hscale1.ne', hresult.1.C_mul hscale2.ne', ?_⟩
  · rw [natDegree_C_mul hscale1.ne']
    exact hUd
  · rw [natDegree_C_mul hscale2.ne']
    exact hGd
  · exact hresult.2.C_mul hscale1 hscale2

end RealRooted.FactorialCompression
