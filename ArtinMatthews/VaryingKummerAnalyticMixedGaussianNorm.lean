module

public import ArtinMatthews.VaryingKummerAnalyticMixedGaussianUnfolding
public import ArtinMatthews.VaryingKummerAnalyticMixedUnitAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification of the mixed archimedean Gaussian with the actual
Euclidean ideal theta coordinates. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Module NumberField NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedTheta
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mixedIdealEmbedding_coordinate (a : I.1) (j : MixedIdealIndex K I) :
    (mixedIdealOrthonormalBasis K I).repr (mixedIdealEmbedding K I a) j =
      (mixedEmbedding.stdBasis K).repr (mixedEmbedding K (a : K))
        (mixedIdealIndexEquiv K I j) := by
  rfl

theorem mixedIdealFlow_norm_sq (a : I.1) (u : logSpace K) :
    ‖logScale (mixedIdealLogScale K I u)
      ((mixedIdealOrthonormalBasis K I).repr (mixedIdealEmbedding K I a))‖^2 =
      ∑ w : InfinitePlace K, (mixedPlaceWeight K u w * w (a : K))^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [logScale_apply, mixedIdealEmbedding_coordinate]
  change (∑ j, (Real.exp (mixedStandardLogScale K u (mixedIdealIndexEquiv K I j)) *
    (mixedEmbedding.stdBasis K).repr (mixedEmbedding K (a : K))
      (mixedIdealIndexEquiv K I j))^2) = _
  rw [(mixedIdealIndexEquiv K I).sum_comp (fun j =>
    (Real.exp (mixedStandardLogScale K u j) *
      (mixedEmbedding.stdBasis K).repr (mixedEmbedding K (a : K)) j)^2),
    Fintype.sum_sum_type,
    InfinitePlace.sum_eq_sum_add_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro w _
    simp only [mixedStandardLogScale, mixedPlaceWeight,
      InfinitePlace.mult_isReal w, Nat.cast_one, div_one,
      mixedEmbedding.stdBasis_apply_isReal]
    change (Real.exp _ * InfinitePlace.embedding_of_isReal w.property (a : K))^2 = _
    rw [mul_pow, mul_pow, ← InfinitePlace.norm_embedding_of_isReal w.property,
      Real.norm_eq_abs, sq_abs]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Fin.sum_univ_two, mixedStandardLogScale,
      mixedEmbedding.stdBasis_apply_isComplex_fst,
      mixedEmbedding.stdBasis_apply_isComplex_snd,
      mixedPlaceWeight, InfinitePlace.mult_isComplex w, Nat.cast_ofNat]
    change (Real.exp _ * (w.1.embedding (a : K)).re)^2 +
      (Real.exp _ * (w.1.embedding (a : K)).im)^2 = _
    rw [← InfinitePlace.norm_embedding_eq]
    simp only [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    ring

/-- The positive nonzero ideal theta kernel is the actual Gaussian norm sum. -/
def mixedIdealPositiveThetaTail (u : logSpace K) (t : ℝ) : ℝ≥0∞ :=
  ∑' a : {a : I.1 // (a : K) ≠ 0}, ENNReal.ofReal
    (Real.exp (-Real.pi * t * ‖logScale (mixedIdealLogScale K I u)
      ((mixedIdealOrthonormalBasis K I).repr (mixedIdealEmbedding K I a.1))‖^2))

theorem mixedIdealPositiveThetaTail_eq (u : logSpace K) (t : ℝ) :
    mixedIdealPositiveThetaTail K I u t =
      ∑' a : nonzeroIdealElements I, mixedArchGaussian K a.1.1 t u := by
  unfold mixedIdealPositiveThetaTail
  simp_rw [mixedIdealFlow_norm_sq]
  change (∑' a : {a : I.1 // (a : K) ≠ 0}, mixedArchGaussian K a.1.1 t u) = _
  exact (nonzeroIdealElementEquiv I).tsum_eq (fun a => mixedArchGaussian K a.1.1 t u)

/-- Actual mixed-signature ideal theta unfolds into its inverse ideal class. -/
theorem mixedIdealPositiveThetaTail_unit_unfold (t : ℝ) :
    (∫⁻ u in mixedUnitLogDomain K, mixedIdealPositiveThetaTail K I u t) =
      (torsionOrder K : ℝ≥0∞) * ∑' J : integralIdealClassFiber I,
        ∫⁻ u, mixedArchGaussian K (idealElementRepresentative I J).1.1 t u := by
  simp_rw [mixedIdealPositiveThetaTail_eq]
  exact mixedArchGaussian_ideal_unfold K I t

end
end ArtinMatthews.VaryingKummerAnalytic
