module

public import ArtinMatthews.VaryingKummerAnalyticGammaIntegral
public import ArtinMatthews.VaryingKummerAnalyticMixedGaussianNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Product Gamma integral over all archimedean places with the actual
multiplicities one (real) and two (complex). This is the separated integral;
the weighted radial/log-coordinate Jacobian is kept as a distinct step. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory
open ArtinMatthews.ReusedArchMellin
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedGammaFactor (s : ℂ) : ℂ :=
  ∏ w : InfinitePlace K,
    ((1/2 : ℂ) * (Real.pi : ℂ)^(-((InfinitePlace.mult w : ℂ)*s/2)) *
      Complex.Gamma ((InfinitePlace.mult w : ℂ)*s/2))

def mixedSeparatedGaussian (a : K) (s : ℂ) (x : InfinitePlace K → ℝ) : ℂ :=
  ∏ w : InfinitePlace K,
    gaussianLogKernel ((InfinitePlace.mult w : ℂ)*s) (Real.pi*(w a)^2) (x w)

theorem mixedSeparatedGaussian_integrable {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) : Integrable (mixedSeparatedGaussian K a s) := by
  apply Integrable.fintype_prod
  intro w
  apply integrable_gaussianLogKernel
  · simpa using mul_pos (Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w))) hs
  · exact mul_pos Real.pi_pos (sq_pos_of_ne_zero ((map_ne_zero w).mpr ha))

theorem mixedArchPower_product {a : K} (ha : a ≠ 0) (s : ℂ) :
    (∏ w : InfinitePlace K, ((|w a| : ℝ) : ℂ)^(-((InfinitePlace.mult w : ℂ)*s))) =
      ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ)^(-s) := by
  have he (w : InfinitePlace K) :
      ((|w a| : ℝ) : ℂ)^(-((InfinitePlace.mult w : ℂ)*s)) =
        ((|(w a)^(InfinitePlace.mult w)| : ℝ) : ℂ)^(-s) := by
    rw [abs_of_nonneg (apply_nonneg w a), abs_of_nonneg (pow_nonneg (apply_nonneg w a) _),
      Complex.ofReal_pow, neg_mul_eq_mul_neg]
    apply Complex.cpow_nat_mul'
    · simp [Complex.arg_ofReal_of_nonneg (apply_nonneg w a), Real.pi_pos]
    · simp [Complex.arg_ofReal_of_nonneg (apply_nonneg w a), Real.pi_pos.le]
  simp_rw [he]
  rw [prod_abs_cpow (fun w : InfinitePlace K => (w a)^(InfinitePlace.mult w))
    (fun w => pow_ne_zero _ ((map_ne_zero w).mpr ha))]
  have hab (w : InfinitePlace K) : |(w a)^(InfinitePlace.mult w)| =
      (w a)^(InfinitePlace.mult w) := abs_of_nonneg (pow_nonneg (apply_nonneg w a) _)
  simp_rw [hab]
  rw [InfinitePlace.prod_eq_abs_norm, Rat.cast_abs]

theorem mixedSeparatedGaussian_integral {a : K} (ha : a ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : InfinitePlace K → ℝ, mixedSeparatedGaussian K a s x) =
      mixedGammaFactor K s * ((|(Algebra.norm ℚ a : ℝ)| : ℝ) : ℂ)^(-s) := by
  unfold mixedSeparatedGaussian
  rw [integral_fintype_prod_volume_eq_prod]
  have he (w : InfinitePlace K) :
      (∫ x : ℝ, gaussianLogKernel ((InfinitePlace.mult w : ℂ)*s)
        (Real.pi*(w a)^2) x) =
      ((1/2 : ℂ) * (Real.pi : ℂ)^(-((InfinitePlace.mult w : ℂ)*s/2)) *
        Complex.Gamma ((InfinitePlace.mult w : ℂ)*s/2)) *
          ((|w a| : ℝ) : ℂ)^(-((InfinitePlace.mult w : ℂ)*s)) := by
    rw [integral_gaussianLogKernel
      (by simpa using mul_pos (Nat.cast_pos.mpr (InfinitePlace.mult_pos (w := w))) hs)
      (mul_pos Real.pi_pos (sq_pos_of_ne_zero ((map_ne_zero w).mpr ha))),
      scaled_cpow Real.pi_pos ((map_ne_zero w).mpr ha)]
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib, mixedArchPower_product K ha]
  rfl

end
end ArtinMatthews.VaryingKummerAnalytic
