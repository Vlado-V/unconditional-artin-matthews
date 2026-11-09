module

public import ArtinMatthews.SourceArchWeightedDiagonalScale
public import ArtinMatthews.SourceKPArchJacquetProfile
public import ArtinMatthews.SourceKPCuspRationalHeight


set_option backward.privateInPublic true
@[expose] public section

/-! The full archimedean product uses the actual embedded frequency and
the same rationally dilated height as the adelic change of variables. -/

namespace ArtinMatthews
open NumberField SourceArchJacquet StandardAdelic
open scoped NumberField AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPTraceJacquetArchProfile_frequency_scale (m : Kˣ) (s : ℂ)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPTraceJacquetArchProfile K hζ m s y =
      (∏ v : InfinitePlace K,
        (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ : ℂ) ^ (2 * s - 1)) *
        sourceKPTraceJacquetArchProfile K hζ 1 s (sourceKPCuspRationalHeight K hζ m y) := by
  classical
  unfold sourceKPTraceJacquetArchProfile sourceArchWeightedProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  let b := sourceKPCuspRationalComplexUnit K hζ m v
  let u : ℂˣ := Units.mk0 (y v : ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne')
  have hu : ‖(u : ℂ)‖ = y v := by
    change ‖(y v : ℂ)‖ = y v
    rw [Complex.norm_real, Real.norm_of_nonneg (hy v).le]
  have hm : sourceKPTraceJacquetProfileFrequency K hζ m v = -(b : ℂ) := rfl
  have hone : sourceKPTraceJacquetProfileFrequency K hζ 1 v = -1 := by
    change -(sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion (1 : K))) = -1
    rw [map_one (algebraMap K v.Completion), map_one (sourceKPArchComplexEquiv K hζ v)]
  have h := sourceArchWeightedDiagonalProfile_frequency_scale sourceArchTraceCharacter s b u
  rw [Units.val_mul, norm_mul, hu] at h
  rw [hm, hone]
  exact h

end
end ArtinMatthews
