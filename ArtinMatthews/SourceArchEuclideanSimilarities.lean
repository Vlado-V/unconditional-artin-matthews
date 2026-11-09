module

public import ArtinMatthews.SourceArchHyperbolicEuclidean


set_option backward.privateInPublic true
@[expose] public section

/-! Exact differentials of the three genuine hyperbolic generators. -/
namespace ArtinMatthews.SourceArchJacquet
open OAI.CubicEisenstein
noncomputable section

lemma sourceArchWeylReflection_norm (x : EuclideanSpatial) :
    ‖euclideanWeylReflection x‖ = ‖x‖ := by
  obtain ⟨h0, h1, h2⟩ := euclideanWeylReflection_apply x
  have hs : ‖euclideanWeylReflection x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2, neg_sq]
  nlinarith [norm_nonneg (euclideanWeylReflection x), norm_nonneg x]

lemma sourceArchComplexDilation_norm (b : ℂ) (x : EuclideanSpatial) :
    ‖euclideanComplexDilation b x‖ = Complex.normSq b * ‖x‖ := by
  obtain ⟨h0, h1, h2⟩ := euclideanComplexDilation_apply b x
  have hc : (b ^ 2).re ^ 2 + (b ^ 2).im ^ 2 = (Complex.normSq b) ^ 2 := by
    simpa [Complex.normSq_apply, sq] using map_pow Complex.normSq b 2
  have hs : ‖euclideanComplexDilation b x‖ ^ 2 =
      (Complex.normSq b) ^ 2 * ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2]
    calc
      _ = ((b ^ 2).re ^ 2 + (b ^ 2).im ^ 2) * (x 0 ^ 2 + x 1 ^ 2) +
          (Complex.normSq b) ^ 2 * x 2 ^ 2 := by ring
      _ = _ := by rw [hc]; ring
  nlinarith [norm_nonneg (euclideanComplexDilation b x), norm_nonneg x,
    Complex.normSq_nonneg b, mul_nonneg (Complex.normSq_nonneg b) (norm_nonneg x)]

def sourceArchWeylDerivative (p : EuclideanSpatial) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanWeylReflection.comp (euclideanInversionDeriv p)

lemma sourceArchWeyl_hasFDerivAt (p : EuclideanSpatial) (hp : p ≠ 0) :
    HasFDerivAt euclideanWeylAction (sourceArchWeylDerivative p) p :=
  euclideanWeylReflection.hasFDerivAt.comp p (euclideanInversion_hasFDerivAt p hp)

lemma sourceArchWeylDerivative_norm (p v : EuclideanSpatial) :
    ‖sourceArchWeylDerivative p v‖ = (1 / ‖p‖) ^ 2 * ‖v‖ := by
  rw [sourceArchWeylDerivative, ContinuousLinearMap.comp_apply, sourceArchWeylReflection_norm]
  simp only [euclideanInversionDeriv, smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (1 / ‖p‖))]
  exact congrArg (fun t : ℝ => (1 / ‖p‖) ^ 2 * t) (((ℝ ∙ p)ᗮ).reflection.norm_map v)

end
end ArtinMatthews.SourceArchJacquet
