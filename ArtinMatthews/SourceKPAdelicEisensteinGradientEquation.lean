module

public import ArtinMatthews.SourceHyperbolicProductGreen
public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceHyperbolicC1Green
public import ArtinMatthews.SourceHyperbolicProductMeasureGreen
public import ArtinMatthews.SourceKPAdelicEisensteinProductC1
public import ArtinMatthews.SourceKPAdelicProductWeakEquation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
