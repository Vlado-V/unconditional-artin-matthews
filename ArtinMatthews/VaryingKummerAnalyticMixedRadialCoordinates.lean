module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaProduct


set_option backward.privateInPublic true
@[expose] public section

/-! Exact weighted radial coordinates for the real and complex archimedean
places. The weighted radial exponent is the number-field degree, not the number
of infinite places. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open ArtinMatthews.ReusedArchMellin
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedRadialLogCoordinates (u : logSpace K) (v : ℝ) (w : InfinitePlace K) : ℝ :=
  mixedRestoredPlaceLog K u w / InfinitePlace.mult w + v/2

theorem mixedRadialLogCoordinates_weighted_sum (u : logSpace K) (v : ℝ) :
    ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) *
      mixedRadialLogCoordinates K u v w = (Module.finrank ℚ K : ℝ)*v/2 := by
  simp only [mixedRadialLogCoordinates, mul_add,
    mul_div_cancel₀ _ InfinitePlace.mult_coe_ne_zero]
  rw [Finset.sum_add_distrib, mixedRestoredPlaceLog_sum, zero_add,
    ← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  ring

def mixedArchEnergy (a : K) (u : logSpace K) : ℝ :=
  ∑ w : InfinitePlace K, (mixedPlaceWeight K u w * w a)^2

def mixedLogRadialKernel (a : K) (s : ℂ) (p : ℝ × logSpace K) : ℂ :=
  Complex.exp ((Module.finrank ℚ K : ℂ)*s/2*(p.1 : ℂ) -
    ((Real.pi*Real.exp p.1*mixedArchEnergy K a p.2 : ℝ) : ℂ))

theorem mixedSeparatedGaussian_coordinates (a : K) (s : ℂ) (v : ℝ) (u : logSpace K) :
    mixedSeparatedGaussian K a s (mixedRadialLogCoordinates K u v) =
      mixedLogRadialKernel K a s (v,u) := by
  unfold mixedSeparatedGaussian
  simp_rw [gaussianLogKernel_scale]
  rw [← Complex.exp_sum]
  unfold mixedLogRadialKernel
  congr 1
  rw [Finset.sum_sub_distrib, ← Complex.ofReal_sum]
  have hs : (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℂ)*s*
      (mixedRadialLogCoordinates K u v w : ℂ)) =
      (Module.finrank ℚ K : ℂ)*s/2*(v : ℂ) := by
    calc
      _ = s * ((∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ)*
          mixedRadialLogCoordinates K u v w : ℝ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [mixedRadialLogCoordinates_weighted_sum]; push_cast; ring
  rw [hs]
  congr 1
  have he (w : InfinitePlace K) :
      Real.pi*(w a*Real.exp (mixedRadialLogCoordinates K u v w))^2 =
        (Real.pi*Real.exp v)*(mixedPlaceWeight K u w*w a)^2 := by
    rw [mixedRadialLogCoordinates, Real.exp_add, mul_pow, mul_pow,
      ← exp_two_mul (v/2), show 2*(v/2)=v by ring]
    unfold mixedPlaceWeight
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  rfl

end
end ArtinMatthews.VaryingKummerAnalytic
