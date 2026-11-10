module

public import ArtinMatthews.SourceKPChartPeriodizationCore
public import ArtinMatthews.SourceKPCompactDirichletCore
public import ArtinMatthews.SourceKPFiniteChartAverage
public import ArtinMatthews.SourceKPChartPeriodizationAverage
public import ArtinMatthews.SourceKPCompactCorePairChart
public import ArtinMatthews.SourceKPCompactEnergyRegularity
public import ArtinMatthews.SourceKPCompactTruncatedChart
public import ArtinMatthews.SourceKPFiniteChartComplexIntegral
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Transfer of a compact weak test through the actual finite-isotropy chart. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "P" => ProductSpace (InfinitePlace K)
local notation "Ω" => productUpper (InfinitePlace K)
local notation "μ" => productVolume (InfinitePlace K)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "T" => sourceKPCompactC2Core K hζ

theorem sourceKPFiniteChart_test_integral (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) (F : Y → ℂ) (G : P → ℂ) (hF : Measurable F)
    (hU : ∀ x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p,
      G x = F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x)))
    (hG0 : ∀ x ∉ sourceKPFiniteChartCoordinateDomain K hζ b p, G x = 0)
    (hF0 : ∀ y ∉ Set.range (sourceKPFiniteChartProjection K hζ b p), F y = 0) :
    (∫ x, G x ∂μ) =
      (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ) * ∫ y, F y ∂μY := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hG0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hF0]
  rw [setIntegral_congr_fun (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet hU]
  exact sourceKPFiniteChart_complex_integral K hζ b p F hF

theorem sourceKPCompactCorePairDensity_zero_outside_left (φ v : T) {y : Y}
    (hy : y ∉ tsupport φ.val) :
    sourceKPCompactCorePairDensity K hζ φ v y = 0 := by
  have he := sourceKPCompactCoreEnergy_zero_outside K hζ φ hy
  have hz : sourceKPCompactCoreGradientAtLinear K hζ y φ = 0 := by
    apply norm_eq_zero.mp
    have hn := sourceKPCompactCoreGradientAt_norm_sq K hζ φ y
    rw [he] at hn
    nlinarith [norm_nonneg (sourceKPCompactCoreGradientAtLinear K hζ y φ)]
  simp [sourceKPCompactCorePairDensity,hz]

theorem sourceKPPeriodizedWeakTest (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) (η : SourceKPFiniteChartTests K hζ b p)
    (w F : Y → ℂ) (hF : Measurable F) (v : T)
    (hloc : ∀ y ∈ tsupport (sourceKPChartPeriodizationCore K hζ b η.val).val,
      v.val =ᶠ[𝓝 y] w)
    (hweak : ∀ ψ : h1Tests (InfinitePlace K) 2,
      (∀ x ∈ tsupport ψ.val, x ∈ Ω ∧
        sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x) ∈
          tsupport (sourceKPChartPeriodizationCore K hζ b η.val).val) →
      (∫ x, productGradientPair ψ.val (sourceKPCompactChartPullback K hζ w b) x ∂μ) =
        ∫ x, star (ψ.val x)*sourceKPCompactChartPullback K hζ F b x ∂μ) :
    sourceKPCompactDirichletCore K hζ (sourceKPChartPeriodizationCore K hζ b η.val) v =
      ∫ y, star ((sourceKPChartPeriodizationCore K hζ b η.val).val y)*F y ∂μY := by
  let φ := sourceKPChartPeriodizationCore K hζ b η.val
  let U := sourceKPFiniteChartCoordinateDomain K hζ b p
  let m : P → Y := fun x => sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x)
  let n := Nat.card (SourceKPFiniteChartStabilizer K hζ b p)
  let ψ : SourceKPFiniteChartTests K hζ b p :=
    (Fintype.card (SourceKPFiniteChartStabilizer K hζ b p) : ℂ) •
      sourceKPFiniteChartTestAverage K hζ b p η
  let A := sourceKPCompactChartPullback K hζ φ.val b
  let V := sourceKPCompactChartPullback K hζ v.val b
  let W := sourceKPCompactChartPullback K hζ w b
  have hu : IsOpen U := sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p
  have hUp : U ⊆ Ω := sourceKPFiniteChartCoordinateDomain_upper K hζ b p
  have hφ : tsupport φ.val ⊆ Set.range (sourceKPFiniteChartProjection K hζ b p) :=
    sourceKPChartPeriodizationCore_support K hζ b p η
  have hm : ContinuousOn m Ω := (sourceKPUpperToCompact_continuous K hζ b).comp_continuousOn
    (sourceKPArchEuclideanUpperMap_continuousOn K)
  have hA (x : P) (hx : x ∈ U) : A x = ψ.val.val x := by
    rw [show A x = φ.val (m x) from sourceKPCompactChartPullback_of_positive K hζ _ b x (hUp hx)]
    obtain ⟨a,ha,rfl⟩ := hx
    change φ.val (sourceKPUpperToCompact K hζ b
      (sourceKPArchEuclideanUpperMap K (sourceKPArchUpperEuclideanMap K a))) = _
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
    exact sourceKPChartPeriodizationCore_local_average K hζ b p η ⟨a,ha⟩
  have hAe {x : P} (hx : x ∈ U) : A =ᶠ[𝓝 x] ψ.val.val := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact hA y hy
  have hsupport (x : P) (hs : x ∈ tsupport ψ.val.val) : x ∈ Ω ∧ m x ∈ tsupport φ.val := by
    have hx := ψ.prop hs
    refine ⟨hUp hx,?_⟩
    have hmc := (hm x (hUp hx)).continuousAt ((productUpper_isOpen _).mem_nhds (hUp hx))
    by_contra hn
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hmc.tendsto
    have he : ψ.val.val =ᶠ[𝓝 x] 0 := by
      filter_upwards [(hAe hx).symm,hz,hu.mem_nhds hx] with y h1 h2 hy
      rw [h1,show A y = φ.val (m y) from sourceKPCompactChartPullback_of_positive K hζ _ b y (hUp hy)]
      exact h2
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hs
  have hpair (x : P) (hx : x ∈ U) :
      productGradientPair ψ.val.val W x = sourceKPCompactCorePairDensity K hζ φ v (m x) := by
    have hh : sourceKPCompactCorePairDensity K hζ φ v (m x) =
        productGradientPair A V x := by
      have h := sourceKPCompactCorePairDensity_chart K hζ φ v b (sourceKPArchEuclideanUpperMap K x)
      rw [sourceKPArchUpperEuclideanMap_right_inverse K x
        (fun i => productUpper_pos (hUp hx) i)] at h
      exact h
    rw [hh]
    have ha := (hAe hx).fderiv_eq (𝕜 := ℝ)
    by_cases hs : x ∈ tsupport ψ.val.val
    · have hmc := (hm x (hUp hx)).continuousAt ((productUpper_isOpen _).mem_nhds (hUp hx))
      have hv := (hloc (m x) (hsupport x hs).2).comp_tendsto hmc.tendsto
      have hVW : V =ᶠ[𝓝 x] W := by
        filter_upwards [hv,hu.mem_nhds hx] with y he hy
        change sourceKPCompactChartPullback K hζ v.val b y =
          sourceKPCompactChartPullback K hζ w b y
        rw [sourceKPCompactChartPullback_of_positive K hζ _ b y (hUp hy),
          sourceKPCompactChartPullback_of_positive K hζ _ b y (hUp hy)]
        exact he
      simp only [productGradientPair,productPartial,ha,hVW.fderiv_eq (𝕜 := ℝ)]
    · rw [fderiv_of_notMem_tsupport ℝ hs] at ha
      simp only [productGradientPair,productPartial,ha,fderiv_of_notMem_tsupport ℝ hs,
        ContinuousLinearMap.zero_apply,star_zero,zero_mul,Finset.sum_const_zero,mul_zero]
  have hl : (∫ x, productGradientPair ψ.val.val W x ∂μ) =
      (n : ℂ) * sourceKPCompactDirichletCore K hζ φ v := by
    apply sourceKPFiniteChart_test_integral K hζ b p
      (sourceKPCompactCorePairDensity K hζ φ v) _ (sourceKPCompactCorePairDensity_continuous K hζ φ v).measurable hpair
    · intro x hx
      have hs : x ∉ tsupport ψ.val.val := fun h => hx (ψ.prop h)
      simp only [productGradientPair,productPartial,fderiv_of_notMem_tsupport ℝ hs,
        ContinuousLinearMap.zero_apply,star_zero,zero_mul,Finset.sum_const_zero,mul_zero]
    · intro y hy
      exact sourceKPCompactCorePairDensity_zero_outside_left K hζ φ v (fun h => hy (hφ h))
  have hr : (∫ x, star (ψ.val.val x)*sourceKPCompactChartPullback K hζ F b x ∂μ) =
      (n : ℂ) * ∫ y, star (φ.val y)*F y ∂μY := by
    apply sourceKPFiniteChart_test_integral K hζ b p (fun y => star (φ.val y)*F y) _
      (φ.prop.1.star.measurable.mul hF)
    · intro x hx
      rw [← hA x hx,show A x = φ.val (m x) from
        sourceKPCompactChartPullback_of_positive K hζ _ b x (hUp hx),
        sourceKPCompactChartPullback_of_positive K hζ _ b x (hUp hx)]
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.prop h)),star_zero,zero_mul]
    · intro y hy
      rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ h)),star_zero,zero_mul]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.card_pos.ne' : Nat.card (SourceKPFiniteChartStabilizer K hζ b p) ≠ 0)
  exact mul_left_cancel₀ hn (hl.symm.trans ((hweak ψ.val hsupport).trans hr))

end
end ArtinMatthews
