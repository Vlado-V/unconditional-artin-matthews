module

public import ArtinMatthews.SpectralJMixedGeometric
public import ArtinMatthews.SpectralJSourceTestSplit


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Complex
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0MixedJ_geometric_parts
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f) =
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJRealTest f)) +
      I * (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJImagTest f)) ∧
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
        (spectralJOddSynthesis f)) =
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis (spectralJRealTest f))) +
      I * (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis (spectralJImagTest f))) := by
  have hR := gamma0MixedJ_geometric_reconstruction (spectralJRealTest f)
    (spectralJRealTest_contDiff f hf) (spectralJRealTest_hasCompactSupport f hc)
    ((spectralJRealTest_tsupport f).trans hp) r s hcop m n hm hn hmn
  have hI := gamma0MixedJ_geometric_reconstruction (spectralJImagTest f)
    (spectralJImagTest_contDiff f hf) (spectralJImagTest_hasCompactSupport f hc)
    ((spectralJImagTest_tsupport f).trans hp) r s hcop m n hm hn hmn
  constructor
  · have hpoint (q : Ioi (0 : ℕ)) :
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f =
          gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJRealTest f) +
          I * gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJImagTest f) := by
      dsimp only [gamma0ABLOppositeGeometricTerm]
      have hparts := congrFun (spectralJTest_parts f)
        (4 * Real.pi * Real.sqrt (|(n : ℝ) * (m : ℝ)|) /
          gamma0TrueWidthModulus (r * s) (gamma0CuspOneOver s) 1 (q.val : ℝ))
      simp only [Pi.add_apply] at hparts
      rw [hparts]
      ring
    simp_rw [hpoint]
    rw [hR.1.of_norm.tsum_add (hI.1.of_norm.mul_left I), tsum_mul_left]
  · have hpoint (q : Ioi (0 : ℕ)) :
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis f) =
          gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJOddSynthesis (spectralJRealTest f)) +
          I * gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
            (spectralJOddSynthesis (spectralJImagTest f)) := by
      dsimp only [gamma0ABLOppositeGeometricTerm]
      rw [spectralJOddSynthesis_parts f hf.continuous hc hp]
      ring
    simp_rw [hpoint]
    rw [hR.2.1.of_norm.tsum_add (hI.2.1.of_norm.mul_left I), tsum_mul_left]

end
end ArtinMatthews
