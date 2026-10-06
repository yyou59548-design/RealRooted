import RealRooted.FactorialCompression.DegreeChanging
import RealRooted.FactorialCompression.Lifting

/-!
# Public factorial-compression theorem surface

This module exposes the factorial-compression results using the native
`RealRooted` predicates.  The internal proof uses a stronger manuscript-level
root-order predicate in order to retain strict inequalities explicitly; the
public surface records the corresponding `StrictInterl` conclusion together
with simple strictly negative roots and exclusion of common roots.
-/

open Polynomial

noncomputable section
namespace RealRooted.FactorialCompression

open Internal

/-- General factorial compression: exact degrees, positive leading
coefficients, simple strictly negative roots, native strict interlacing, and no
common root.  Repeated roots are allowed in the input polynomial. -/
theorem factorialCompression_geometry {N ell : ℕ} {a : ℝ} {p : ℝ[X]}
    (hN : 1 ≤ N) (hell : ell ≤ N) (ha : 0 < a)
    (hpdegree : p.natDegree = N) (hpsplit : p.Splits)
    (hppos : 0 < p.leadingCoeff) (hproots : ∀ r ∈ p.roots, r < 0) :
    (compression N ell p).natDegree = (N + ell) / 2 ∧
    (compression (N + 1) ell (nextPolynomial a p)).natDegree = (N + ell + 1) / 2 ∧
    HasPosLeadingCoeff (compression N ell p) ∧
    HasPosLeadingCoeff (compression (N + 1) ell (nextPolynomial a p)) ∧
    (compression N ell p).Splits ∧
    HasSimpleRoots (compression N ell p) ∧
    (∀ r ∈ (compression N ell p).roots, r < 0) ∧
    (compression (N + 1) ell (nextPolynomial a p)).Splits ∧
    HasSimpleRoots (compression (N + 1) ell (nextPolynomial a p)) ∧
    (∀ r ∈ (compression (N + 1) ell (nextPolynomial a p)).roots, r < 0) ∧
    StrictInterl (compression N ell p)
      (compression (N + 1) ell (nextPolynomial a p)) ∧
    (∀ r, (compression N ell p).IsRoot r →
      ¬ (compression (N + 1) ell (nextPolynomial a p)).IsRoot r) := by
  obtain ⟨hdeg₁, hdeg₂, hroot₁, hroot₂, hinter⟩ :=
    factorial_compression hN hell ha hpdegree hpsplit hppos hproots
  exact ⟨hdeg₁, hdeg₂, hinter.1, hinter.2.1,
    hroot₁.2.1, hroot₁.hasSimpleRoots, hroot₁.2.2.2,
    hroot₂.2.1, hroot₂.hasSimpleRoots, hroot₂.2.2.2,
    hinter.to_upstream, hinter.no_common_root⟩

/-- Adjacent-degree gamma lifting in the native `RealRooted` interface.
The explicit no-common-root hypothesis upgrades the library interlacing
relation to the strict manuscript root order used by the internal proof. -/
theorem twoBranchLifting_geometry {n : ℕ} {A B : ℝ[X]} (hn : 2 ≤ n)
    (hAdegree : A.natDegree = (n - 1) / 2)
    (hBdegree : B.natDegree = n / 2)
    (hApos : HasPosLeadingCoeff A) (hBpos : HasPosLeadingCoeff B)
    (hAneg : ∀ r ∈ A.roots, r < 0) (hBneg : ∀ r ∈ B.roots, r < 0)
    (hpair : StrictInterl A B)
    (hno : ∀ r, ¬ (A.IsRoot r ∧ B.IsRoot r)) :
    (gammaTransform (n - 1) A).natDegree = n - 1 ∧
    (gammaTransform n B).natDegree = n ∧
    HasSimpleRoots (gammaTransform (n - 1) A) ∧
    HasSimpleRoots (gammaTransform n B) ∧
    (∀ r ∈ (gammaTransform (n - 1) A).roots, r < 0) ∧
    (∀ r ∈ (gammaTransform n B).roots, r < 0) ∧
    StrictInterl (gammaTransform (n - 1) A) (gammaTransform n B) ∧
    (∀ r, (gammaTransform (n - 1) A).IsRoot r →
      ¬ (gammaTransform n B).IsRoot r) := by
  have hsimp := hpair.hasSimpleRoots_of_no_common_root hno
  have hAinternal : Internal.SimpleNegativeRoots A :=
    ⟨hpair.1.1, hpair.1.2, hsimp.1.roots_nodup, hAneg⟩
  have hBinternal : Internal.SimpleNegativeRoots B :=
    ⟨hpair.2.1.1, hpair.2.1.2, hsimp.2.roots_nodup, hBneg⟩
  have hpairInternal : Internal.ManuscriptStrictInterl A B :=
    Internal.manuscriptStrictInterl_of_upstream_no_common hpair hApos hBpos hno
  obtain ⟨hdeg₁, hdeg₂, hroot₁, hroot₂, hinter⟩ :=
    two_branch_lifting hn hAdegree hBdegree hAinternal hBinternal
      hApos hBpos hpairInternal
  exact ⟨hdeg₁, hdeg₂, hroot₁.hasSimpleRoots, hroot₂.hasSimpleRoots,
    hroot₁.2.2.2, hroot₂.2.2.2, hinter.to_upstream, hinter.no_common_root⟩

end RealRooted.FactorialCompression
