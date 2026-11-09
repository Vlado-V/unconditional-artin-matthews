module

public import ArtinMatthews.SourceKPArchJacquetFrequencyScale
public import ArtinMatthews.SourceArchUnitFrequencyProfile


set_option backward.privateInPublic true
@[expose] public section

/-! The arbitrary nonzero-frequency profile at the exceptional parameter
is positive and real, using the exact rational-height dilation. -/

namespace ArtinMatthews
open NumberField SourceArchJacquet StandardAdelic
open scoped NumberField AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPTraceJacquetArchProfile_oneSixth_positive (m : Kˣ)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    0 < (sourceKPTraceJacquetArchProfile K hζ m (1 / 6) y).re ∧
      (sourceKPTraceJacquetArchProfile K hζ m (1 / 6) y).im = 0 := by
  classical
  let Y := sourceKPCuspRationalHeight K hζ m y
  let a (v : InfinitePlace K) := ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖
  let P : ℝ := ∏ v : InfinitePlace K, a v ^ (-(2 / 3) : ℝ)
  have ha (v : InfinitePlace K) : 0 < a v :=
    norm_pos_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero
  have hP : 0 < P := Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (ha v) _
  have hPcast : (∏ v : InfinitePlace K, (a v : ℂ) ^ (2 * (1 / 6 : ℂ) - 1)) = (P : ℂ) := by
    have he : 2 * (1 / 6 : ℂ) - 1 = ((-(2 / 3) : ℝ) : ℂ) := by push_cast; norm_num
    calc
      _ = ∏ v : InfinitePlace K, ((a v ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) := by
        apply Finset.prod_congr rfl
        intro v _
        rw [he]
        exact (Complex.ofReal_cpow (ha v).le _).symm
      _ = _ := (map_prod Complex.ofRealHom (fun v : InfinitePlace K => a v ^ (-(2 / 3) : ℝ)) _).symm
  have hone : sourceKPTraceJacquetProfileFrequency K hζ (1 : Kˣ) = fun _ => -1 := by
    funext v
    change -(sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion (1 : K))) = -1
    rw [map_one (algebraMap K v.Completion), map_one (sourceKPArchComplexEquiv K hζ v)]
  have hU : 0 < (sourceKPTraceJacquetArchProfile K hζ 1 (1 / 6) Y).re ∧
      (sourceKPTraceJacquetArchProfile K hζ 1 (1 / 6) Y).im = 0 := by
    unfold sourceKPTraceJacquetArchProfile
    rw [hone]
    exact sourceArchUnitFrequencyProduct_positive Y (sourceKPCuspRationalHeight_pos K hζ m y hy)
  have hscale := sourceKPTraceJacquetArchProfile_frequency_scale K hζ m (1 / 6) y hy
  change _ = (∏ v : InfinitePlace K, (a v : ℂ) ^ (2 * (1 / 6 : ℂ) - 1)) *
    sourceKPTraceJacquetArchProfile K hζ 1 (1 / 6) Y at hscale
  rw [hPcast] at hscale
  constructor
  · rw [hscale, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hP hU.1
  · rw [hscale, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hU.2, mul_zero]

end
end ArtinMatthews
