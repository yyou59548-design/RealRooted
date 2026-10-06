import RealRooted.FactorialCompression.Definitions
import RealRooted.FactorialCompression.Internal.Scaling

open Polynomial RealRooted RealRooted.FactorialCompression.Internal
noncomputable section
namespace RealRooted.FactorialCompression

/-- The explicit positive constant/negative linear root convention in (1.2). -/
theorem constant_linear_geometry {c b d : ℝ} (hc : 0 < c)
    (hb : 0 < b) (hd : 0 < d) :
    (C c : ℝ[X]).natDegree = 0 ∧
    (C b + C d * X : ℝ[X]).natDegree = 1 ∧
    SimpleNegativeRoots (C c) ∧
    SimpleNegativeRoots (C b + C d * X) ∧
    ManuscriptStrictInterl (C c) (C b + C d * X) := by
  let g : ℝ[X] := C b + C d * X
  have hfactor : g = C d * (X - C (-b / d)) := by
    dsimp [g]
    simp only [mul_sub, ← C_mul]
    rw [show d * (-b / d) = -b by field_simp]
    simp
    ring
  have hgdegree : g.natDegree = 1 := by
    rw [hfactor, natDegree_C_mul hd.ne', natDegree_X_sub_C]
  have hgroots : g.roots = {-b / d} := by
    rw [hfactor, roots_C_mul _ hd.ne', roots_X_sub_C]
  have hgpos : 0 < g.leadingCoeff := by
    rw [← coeff_natDegree, hgdegree]
    simpa [g] using hd
  have hg : SimpleNegativeRoots g := by
    refine ⟨?_, Splits.of_natDegree_eq_one hgdegree, ?_, ?_⟩
    · intro hz
      simp [hz] at hgdegree
    · simp [hgroots]
    · intro r hr
      simp only [hgroots, Multiset.mem_singleton] at hr
      subst r
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hb) hd
  have hf : SimpleNegativeRoots (C c : ℝ[X]) := by
    refine ⟨?_, Splits.C c, ?_, ?_⟩
    · simpa using hc.ne'
    · simp
    · simp
  refine ⟨by simp, hgdegree, hf, hg, ?_⟩
  refine ⟨by simpa using hc, hgpos, hf.2.1, hg.2.1,
    [], [-b / d], by simp, by simp, by simp, ?_,
    Or.inl ⟨by simp, True.intro⟩⟩
  simpa [g] using hgroots.symm

/-- Exact coefficient computation in the N=1, ell=0 boundary case.
No information about a numerical instance is used. -/
theorem boundary_compressions (a : ℝ) (p : ℝ[X]) :
    compression 1 0 p = C (p.coeff 0) ∧
    compression 2 0 (nextPolynomial a p) =
      C (a * p.coeff 0) + C (p.coeff 0 + (a + 1) * p.coeff 1) * X := by
  constructor
  · simp [compression, mu, Finset.sum_range_succ]
  · simp [compression, mu, Finset.sum_range_succ, nextPolynomial,
      add_mul, coeff_derivative]
    ring

/-- The m=1 case of Theorem 1.1, for every real a>0 and degree-one p. -/
theorem factorial_compression_boundary {a : ℝ} {p : ℝ[X]}
    (ha : 0 < a) (hpdegree : p.natDegree = 1) (hpsplit : p.Splits)
    (hppos : 0 < p.leadingCoeff) (hproots : ∀ r ∈ p.roots, r < 0) :
    (compression 1 0 p).natDegree = 0 ∧
    (compression 2 0 (nextPolynomial a p)).natDegree = 1 ∧
    SimpleNegativeRoots (compression 1 0 p) ∧
    SimpleNegativeRoots (compression 2 0 (nextPolynomial a p)) ∧
    ManuscriptStrictInterl (compression 1 0 p)
      (compression 2 0 (nextPolynomial a p)) := by
  have hp0 := coeff_zero_pos_of_negativeRoots hpsplit hppos hproots
  have hp1 : 0 < p.coeff 1 := by
    simpa only [← hpdegree, coeff_natDegree] using hppos
  rw [(boundary_compressions a p).1, (boundary_compressions a p).2]
  exact constant_linear_geometry hp0 (mul_pos ha hp0)
    (add_pos hp0 (mul_pos (by linarith) hp1))

end RealRooted.FactorialCompression
