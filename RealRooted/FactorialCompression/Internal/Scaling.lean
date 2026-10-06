import RealRooted.FactorialCompression.Internal.RootSigns

open Polynomial
noncomputable section
namespace RealRooted.FactorialCompression.Internal

theorem SimpleNegativeRoots.C_mul {p : ℝ[X]} (hp : SimpleNegativeRoots p)
    {a : ℝ} (ha : a ≠ 0) : SimpleNegativeRoots (C a * p) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr ha) hp.1, hp.2.1.C_mul a, ?_, ?_⟩
  · simpa [roots_C_mul p ha] using hp.2.2.1
  · simpa [roots_C_mul p ha] using hp.2.2.2

theorem ManuscriptStrictInterl.C_mul {f g : ℝ[X]}
    (hfg : ManuscriptStrictInterl f g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ManuscriptStrictInterl (C a * f) (C b * g) := by
  rcases hfg with ⟨hfpos, hgpos, hfs, hgs, rs, ss, hrs, hss, hrf, hsg, horder⟩
  refine ⟨?_, ?_, hfs.C_mul a, hgs.C_mul b, rs, ss, hrs, hss, ?_, ?_, horder⟩
  · simpa [leadingCoeff_mul] using mul_pos ha hfpos
  · simpa [leadingCoeff_mul] using mul_pos hb hgpos
  · simpa [roots_C_mul f ha.ne'] using hrf
  · simpa [roots_C_mul g hb.ne'] using hsg

end RealRooted.FactorialCompression.Internal
