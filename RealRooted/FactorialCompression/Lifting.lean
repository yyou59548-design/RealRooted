import RealRooted.FactorialCompression.Internal.RootTransfer
import RealRooted.FactorialCompression.Internal.Multiplier

open Polynomial RealRooted RealRooted.FactorialCompression.Internal
noncomputable section
namespace RealRooted.FactorialCompression

/-- Authoritative manuscript Lemma 4.1, with exactly its positive leading
coefficients, simple negative roots, degrees and strict oriented input.
Coefficient nonnegativity and the nonzero constant terms are derived. -/
theorem two_branch_lifting {n : ℕ} {A B : ℝ[X]} (hn : 2 ≤ n)
    (hAdegree : A.natDegree = (n - 1) / 2)
    (hBdegree : B.natDegree = n / 2)
    (hA : SimpleNegativeRoots A) (hB : SimpleNegativeRoots B)
    (hApos : 0 < A.leadingCoeff) (hBpos : 0 < B.leadingCoeff)
    (hpair : ManuscriptStrictInterl A B) :
    (gammaTransform (n - 1) A).natDegree = n - 1 ∧
    (gammaTransform n B).natDegree = n ∧
    SimpleNegativeRoots (gammaTransform (n - 1) A) ∧
    SimpleNegativeRoots (gammaTransform n B) ∧
    ManuscriptStrictInterl (gammaTransform (n - 1) A) (gammaTransform n B) := by
  have heq : n - 1 + 1 = n := by lia
  have hAnn := (isPFPolynomial_of_negativeRoots hA.2.1 hApos hA.2.2.2).hasNonnegCoeffs
  have hBnn := (isPFPolynomial_of_negativeRoots hB.2.1 hBpos hB.2.2.2).hasNonnegCoeffs
  have hA0 := coeff_zero_pos_of_negativeRoots hA.2.1 hApos hA.2.2.2
  have hB0 := coeff_zero_pos_of_negativeRoots hB.2.1 hBpos hB.2.2.2
  simpa only [heq] using gamma_to_descent_strict hAdegree
    (by simpa only [heq] using hBdegree) hAnn hBnn hA0 hB0 hpair

end RealRooted.FactorialCompression
