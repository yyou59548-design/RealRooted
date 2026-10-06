import RealRooted.FactorialCompression.Internal.RootSigns
import RealRooted.GammaTransform.ProperPosition

/- The two-branch gamma transform uses the upstream reciprocal-root proof.
The weak upstream conclusion is upgraded only after excluding every shared
root, including the parity-dependent root -1. This file is a candidate until
the exact pinned environment has checked it. -/

open Polynomial
open RealRooted

noncomputable section

namespace RealRooted.FactorialCompression.Internal

theorem gammaTransform_degree {d : ℕ} {γ : ℝ[X]} (hzero : γ.coeff 0 ≠ 0) :
    (gammaTransform d γ).natDegree = d := by
  apply Nat.le_antisymm (natDegree_gammaTransform_le d γ)
  exact le_natDegree_of_ne_zero (by simpa using hzero)

/-- Exact multiplicity of the parity root -1 at full floor degree. -/
theorem gammaTransform_center_multiplicity {d : ℕ} {γ : ℝ[X]}
    (hdegree : γ.natDegree = d / 2) (hγ : γ ≠ 0) :
    (gammaTransform d γ).rootMultiplicity (-1) = d % 2 := by
  rw [rootMultiplicity_neg_one_gammaTransform hdegree.le hγ, hdegree]
  lia

/-- The two inverse branches and central parity root transfer a strict gamma
pair of full floor degrees to a strict descent pair in adjacent degrees.
No gamma interlacing theorem is assumed as an external mathematical input:
this is the reusable transfer lemma whose input is a previously proved pair. -/
theorem gamma_to_descent_strict {d : ℕ} {γ δ : ℝ[X]}
    (hγdegree : γ.natDegree = d / 2)
    (hδdegree : δ.natDegree = (d + 1) / 2)
    (hγnn : HasNonnegCoeffs γ) (hδnn : HasNonnegCoeffs δ)
    (hγ0 : 0 < γ.coeff 0) (hδ0 : 0 < δ.coeff 0)
    (hpair : ManuscriptStrictInterl γ δ) :
    (gammaTransform d γ).natDegree = d ∧
      (gammaTransform (d + 1) δ).natDegree = d + 1 ∧
      SimpleNegativeRoots (gammaTransform d γ) ∧
      SimpleNegativeRoots (gammaTransform (d + 1) δ) ∧
      ManuscriptStrictInterl (gammaTransform d γ) (gammaTransform (d + 1) δ) := by
  have hγbound : γ.natDegree ≤ d / 2 := hγdegree.le
  have hδbound : δ.natDegree ≤ (d + 1) / 2 := hδdegree.le
  have hweak : StrictInterl (gammaTransform d γ) (gammaTransform (d + 1) δ) :=
    (strictInterl_gammaTransform_succ_iff hγbound hδbound hγnn hδnn
      (ne_of_gt hγ0) (ne_of_gt hδ0)).2 hpair.to_upstream
  have hno : ∀ r : ℝ,
      ¬ ((gammaTransform d γ).IsRoot r ∧ (gammaTransform (d + 1) δ).IsRoot r) := by
    intro r hr
    by_cases hrcenter : r = -1
    · subst r
      rcases Nat.even_or_odd d with heven | hodd
      · rcases heven with ⟨m, hm⟩
        have hdm : d = 2 * m := by lia
        have hγm : γ.natDegree = m := by rw [hγdegree, hdm]; simp
        have hne : (gammaTransform d γ).eval (-1) ≠ 0 := by
          rw [hdm, gammaTransform_even_eval_neg_one, ← hγm, coeff_natDegree]
          exact mul_ne_zero (ne_of_gt hpair.1)
            (pow_ne_zero _ (by norm_num))
        exact hne hr.1
      · rcases hodd with ⟨m, hm⟩
        have hdm : d + 1 = 2 * (m + 1) := by lia
        have hδm : δ.natDegree = m + 1 := by rw [hδdegree, hdm]; simp
        have hne : (gammaTransform (d + 1) δ).eval (-1) ≠ 0 := by
          rw [hdm, gammaTransform_even_eval_neg_one, ← hδm, coeff_natDegree]
          exact mul_ne_zero (ne_of_gt hpair.2.1)
            (pow_ne_zero _ (by norm_num))
        exact hne hr.2
    · exact hpair.not_common_root (r / (1 + r) ^ 2)
        ⟨isRoot_gamma_of_isRoot_gammaTransform hγbound hrcenter hr.1,
          isRoot_gamma_of_isRoot_gammaTransform hδbound hrcenter hr.2⟩
  have hTγnn : HasNonnegCoeffs (gammaTransform d γ) :=
    hasNonnegCoeffs_gammaTransform hγnn
  have hTδnn : HasNonnegCoeffs (gammaTransform (d + 1) δ) :=
    hasNonnegCoeffs_gammaTransform hδnn
  have hsimp := hweak.hasSimpleRoots_of_no_common_root hno
  have hTγnegative : ∀ r ∈ (gammaTransform d γ).roots, r < 0 := by
    intro r hr
    have hrle := roots_nonpos_of_hasNonnegCoeffs hTγnn r hr
    have hrne : r ≠ 0 := by
      intro heq
      subst r
      have hroot := isRoot_of_mem_roots hr
      have hpositive : 0 < (gammaTransform d γ).eval 0 := by simpa using hγ0
      exact (ne_of_gt hpositive) (Polynomial.IsRoot.def.mp hroot)
    exact lt_of_le_of_ne hrle hrne
  have hTδnegative : ∀ r ∈ (gammaTransform (d + 1) δ).roots, r < 0 := by
    intro r hr
    have hrle := roots_nonpos_of_hasNonnegCoeffs hTδnn r hr
    have hrne : r ≠ 0 := by
      intro heq
      subst r
      have hroot := isRoot_of_mem_roots hr
      have hpositive : 0 < (gammaTransform (d + 1) δ).eval 0 := by simpa using hδ0
      exact (ne_of_gt hpositive) (Polynomial.IsRoot.def.mp hroot)
    exact lt_of_le_of_ne hrle hrne
  exact ⟨gammaTransform_degree (ne_of_gt hγ0), gammaTransform_degree (ne_of_gt hδ0),
    ⟨hweak.1.1, hweak.1.2, hsimp.1.roots_nodup, hTγnegative⟩,
    ⟨hweak.2.1.1, hweak.2.1.2, hsimp.2.roots_nodup, hTδnegative⟩,
    manuscriptStrictInterl_of_upstream_no_common hweak
      (hTγnn.pos_leadingCoeff hweak.1.1) (hTδnn.pos_leadingCoeff hweak.2.1.1) hno⟩

end RealRooted.FactorialCompression.Internal
