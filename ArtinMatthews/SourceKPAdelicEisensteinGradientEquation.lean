module

public import ArtinMatthews.SourceKPAdelicEisensteinProductC1
public import ArtinMatthews.SourceKPAdelicProductWeakEquation
public import ArtinMatthews.SourceHyperbolicC1Green


set_option backward.privateInPublic true
@[expose] public section

/-! The actual initial Eisenstein family satisfies the variational
eigen-equation for its genuine weighted first derivatives. -/

namespace ArtinMatthews
open NumberField MeasureTheory OAI.CubicEisenstein SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicEisensteinProductChart_gradient_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) {φ : ProductSpace (InfinitePlace K) → ℂ}
    (hφ : ContDiffOn ℝ 2 φ (productUpper (InfinitePlace K)))
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ productUpper (InfinitePlace K)) :
    Integrable (productGradientPair φ (sourceKPAdelicEisensteinProductChart K hζ s q))
      (productVolume (InfinitePlace K)) :=
  productGradientPair_integrable_C1
    (fun p hp => sourceKPAdelicEisensteinProductChart_contDiffAt K hζ hs q p
      (fun v => productUpper_pos hp v))
    (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp

theorem sourceKPAdelicEisensteinProductChart_tested_laplacian_integrable {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) {φ : ProductSpace (InfinitePlace K) → ℂ}
    (hφ : ContDiffOn ℝ 2 φ (productUpper (InfinitePlace K)))
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ productUpper (InfinitePlace K)) :
    Integrable (fun p => star (sourceArchProductCoordinateLaplacian φ p)*
      sourceKPAdelicEisensteinProductChart K hζ s q p) (productVolume (InfinitePlace K)) :=
  product_native_adjoint_integrable_C1
    (fun p hp => sourceKPAdelicEisensteinProductChart_contDiffAt K hζ hs q p
      (fun v => productUpper_pos hp v))
    (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp

theorem sourceKPAdelicEisensteinProductChart_gradient_eigen {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ) {φ : ProductSpace (InfinitePlace K) → ℂ}
    (hφ : ContDiffOn ℝ 2 φ (productUpper (InfinitePlace K)))
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ productUpper (InfinitePlace K)) :
    (∫ p, productGradientPair φ (sourceKPAdelicEisensteinProductChart K hζ s q) p
      ∂productVolume (InfinitePlace K)) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
        ∫ p, star (φ p)*sourceKPAdelicEisensteinProductChart K hζ s q p
          ∂productVolume (InfinitePlace K) := by
  rw [product_native_gradient_green_C1_on
    (sourceKPAdelicEisensteinProductChart_contDiffOn K hζ hs q) hφ hc hsupp]
  exact sourceKPAdelicEisensteinProductChart_test_eigen K hζ hs q
    (product_test_contDiff_of_contDiffOn hφ hsupp) hc hsupp

end
end ArtinMatthews
