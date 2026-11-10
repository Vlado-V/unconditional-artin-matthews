module

public import ArtinMatthews.SourceHyperbolicProductGreen
public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceHyperbolicH1Measure
public import ArtinMatthews.SourceHyperbolicProductAdjointCalculus
public import ArtinMatthews.SourceHyperbolicProductAdjointGreen
public import ArtinMatthews.SourceHyperbolicProductSlices
public import ArtinMatthews.SourceKPAdelicProductTestSum
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
public import Mathlib.Order.CompletePartialOrder
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

/-! The actual Eisenstein series satisfies the full product-hyperbolic
tested eigen-equation in the proved initial half-plane. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory OAI.CubicEisenstein
open SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField ContDiff BigOperators Classical
noncomputable section

private theorem productTest_star_tsupport {ι : Type*} (f : ProductSpace ι → ℂ) :
    tsupport (fun p => star (f p)) = tsupport f := by
  unfold tsupport
  congr 1
  ext p
  simp only [Function.mem_support,star_ne_zero]

private theorem productTest_laplacian_continuous {ι : Type*} [Fintype ι]
    {φ : ProductSpace ι → ℂ} (hφ : ContDiff ℝ 2 φ) : Continuous (productLaplacian φ) := by
  have hfirst (i : ι) (j : Fin 3) : ContDiff ℝ 1 (productPartial φ i j) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  have hsecond (i : ι) (j : Fin 3) : Continuous (productPartial (productPartial φ i j) i j) :=
    (((hfirst i j).fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  unfold productLaplacian blockLaplacian
  apply continuous_finsetSum
  intro i _
  exact ((by fun_prop : Continuous (fun p : ProductSpace ι => -(p i 2 : ℂ)^2)).mul
    (continuous_finsetSum Finset.univ (fun j _ => hsecond i j))).add
      ((by fun_prop : Continuous (fun p : ProductSpace ι => (p i 2 : ℂ))).mul
        (hfirst i 2).continuous)

private theorem productTest_laplacian_tsupport {ι : Type*} [Fintype ι]
    (φ : ProductSpace ι → ℂ) : tsupport (productLaplacian φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  by_contra hn
  exact hp (productLaplacian_zero_notMem_tsupport hn)

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRationalProductChart_test_eigen (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (c : SourceKPRationalBorelCoset K)
    {φ : ProductSpace (InfinitePlace K) → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ productUpper (InfinitePlace K)) :
    (∫ p, star (productLaplacian φ p)*sourceKPAdelicRationalProductChart K hζ s q c p
      ∂productVolume (InfinitePlace K)) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
        ∫ p, star (φ p)*sourceKPAdelicRationalProductChart K hζ s q c p
          ∂productVolume (InfinitePlace K) := by
  have hf : ∀ p ∈ productUpper (InfinitePlace K),
      ContDiffAt ℝ 2 (sourceKPAdelicRationalProductChart K hζ s q c) p := by
    intro p hp
    exact (sourceKPAdelicRationalProductChart_contDiffAt K hζ s q c p
      (fun v => productUpper_pos hp v)).of_le (by simp)
  rw [product_adjoint_green_hyperbolic hf hφ hc hsupp]
  have he : (fun p => star (φ p)*productLaplacian
      (sourceKPAdelicRationalProductChart K hζ s q c) p) =
      fun p => ((InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2))*
        (star (φ p)*sourceKPAdelicRationalProductChart K hζ s q c p) := by
    funext p
    by_cases hp : p ∈ productUpper (InfinitePlace K)
    · rw [productLaplacian_eq_native hf hp,sourceKPAdelicRationalProductChart_laplacian
        K hζ s q c p (fun v => productUpper_pos hp v)]
      ring
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
      rw [hz,star_zero,zero_mul,zero_mul,mul_zero]
  rw [he,integral_const_mul]

theorem sourceKPAdelicEisensteinProductChart_test_eigen {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (q : SourceKPAdelicProjective K hζ)
    {φ : ProductSpace (InfinitePlace K) → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ productUpper (InfinitePlace K)) :
    (∫ p, star (sourceArchProductCoordinateLaplacian φ p)*sourceKPAdelicEisensteinProductChart K hζ s q p
      ∂productVolume (InfinitePlace K)) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
        ∫ p, star (φ p)*sourceKPAdelicEisensteinProductChart K hζ s q p
          ∂productVolume (InfinitePlace K) := by
  have hleft : (∫ p, star (sourceArchProductCoordinateLaplacian φ p)*
      sourceKPAdelicEisensteinProductChart K hζ s q p ∂productVolume (InfinitePlace K)) =
      ∫ p, star (productLaplacian φ p)*sourceKPAdelicEisensteinProductChart K hζ s q p
        ∂productVolume (InfinitePlace K) := by
    apply integral_congr_ae
    filter_upwards [productVolume_ae_upper (ι := InfinitePlace K)] with p hp
    rw [productLaplacian_eq_native (fun _ _ => hφ.contDiffAt) hp]
  rw [hleft]
  have hL : HasCompactSupport (productLaplacian φ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (productTest_laplacian_tsupport φ)
  have hφStar : HasCompactSupport (fun p => star (φ p)) := by
    change IsCompact (tsupport (fun p => star (φ p)))
    rw [productTest_star_tsupport]
    exact hc
  have hLStar : HasCompactSupport (fun p => star (productLaplacian φ p)) := by
    change IsCompact (tsupport (fun p => star (productLaplacian φ p)))
    rw [productTest_star_tsupport]
    exact hL
  have hφSupport : tsupport (fun p => star (φ p)) ⊆ productUpper (InfinitePlace K) := by
    rw [productTest_star_tsupport]
    exact hsupp
  have hLSupport : tsupport (fun p => star (productLaplacian φ p)) ⊆ productUpper (InfinitePlace K) := by
    rw [productTest_star_tsupport]
    exact (productTest_laplacian_tsupport φ).trans hsupp
  rw [sourceKPAdelicProductChart_test_integral_tsum K hζ hs q
    (productTest_laplacian_continuous hφ).star hLStar hLSupport,
    sourceKPAdelicProductChart_test_integral_tsum K hζ hs q hφ.continuous.star hφStar hφSupport]
  simp_rw [sourceKPAdelicRationalProductChart_test_eigen K hζ s q _ hφ hc hsupp]
  exact tsum_mul_left

end
end ArtinMatthews
