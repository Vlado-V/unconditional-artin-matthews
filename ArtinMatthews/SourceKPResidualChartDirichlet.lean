module

public import ArtinMatthews.SourceKPResidualChartGradient
public import ArtinMatthews.SourceKPCompactFormLocalization
public import ArtinMatthews.SourceKPCompactH1WeakTests
public import ArtinMatthews.SourceKPPeriodizedWeakTest
import ArtinMatthews.SourceKPCompactNativeTestSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The exact periodized Dirichlet pairing descends to an arbitrary test on the plateau. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
open scoped InnerProductSpace ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "I" => InfinitePlace K
local notation "X" => ProductSpace I
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "Ω" => productUpper I
local notation "V" => sourceKPResidualChartPlateauDomain K hζ b p
local notation "q" => sourceKPCompactCoordinateProjection K hζ b
local notation "ν" => productVolume I
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "Tests" => SourceKPFiniteChartTests K hζ b p
local notation "C" => sourceKPCompactC2Core K hζ
local notation "L" => sourceKPCompactH1Localization K hζ b p
local notation "G" => h1EnergyGradient I
local notation "A" => sourceKPFiniteChartTestAverage K hζ b p
local notation "P" => sourceKPChartPeriodizationCore K hζ b

theorem sourceKPCompactCoreLocalized_dirichlet_periodized (η φ : Tests)
    (hηinv : ∀ (γ : H) (x : X), x ∈ Ω →
      η.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) = η.val.val x)
    {W : Set Y} (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1)
    (hφ : tsupport φ.val.val ⊆ V W) (f : C) :
    sourceKPCompactDirichletCore K hζ (P φ.val) f =
      inner ℂ (h1TestGradient φ.val)
        (h1TestGradient (sourceKPCompactCoreLocalized K hζ f b p η).val) := by
  let F := P φ.val
  let g := sourceKPCompactCoreLocalized K hζ f b p η
  let ψ : Tests := (Fintype.card H : ℂ) • A φ
  let Fcoord := sourceKPCompactChartPullback K hζ F.val b
  let fcoord := sourceKPCompactChartPullback K hζ f.val b
  have hU := sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p
  have hUp := sourceKPFiniteChartCoordinateDomain_upper K hζ b p
  have hF : tsupport F.val ⊆ W := by
    intro y hy
    obtain ⟨z,⟨x,hx,rfl⟩,rfl⟩ := sourceKPChartPeriodizationGlobal_tsupport K hζ b φ.val hy
    exact (hφ hx).2
  have hFψ {x : X} (hx : x ∈ U) : Fcoord x = ψ.val.val x := by
    rw [show Fcoord x = F.val (q x) from
      sourceKPCompactChartPullback_of_positive K hζ F.val b x (hUp hx)]
    obtain ⟨z,hz,rfl⟩ := hx
    change F.val (sourceKPUpperToCompact K hζ b
      (sourceKPArchEuclideanUpperMap K (sourceKPArchUpperEuclideanMap K z))) = _
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
    exact sourceKPChartPeriodizationCore_local_average K hζ b p φ ⟨z,hz⟩
  have hFe {x : X} (hx : x ∈ U) : Fcoord =ᶠ[𝓝 x] ψ.val.val := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hFψ hy
  have hψ : tsupport ψ.val.val ⊆ V W := by
    intro x hx
    have hxU := ψ.prop hx
    refine ⟨hxU, ?_⟩
    change q x ∈ W
    by_contra hn
    have hc := ((sourceKPCompactCoordinateProjection_continuousOn K hζ b) x (hUp hxU)).continuousAt
      ((productUpper_isOpen I).mem_nhds (hUp hxU))
    have hz := (notMem_tsupport_iff_eventuallyEq.mp (fun hs => hn (hF hs))).comp_tendsto hc.tendsto
    have he : ψ.val.val =ᶠ[𝓝 x] 0 := by
      filter_upwards [(hFe hxU).symm, hz, hU.mem_nhds hxU] with y hy hz hyU
      rw [hy, show Fcoord y = F.val (q y) from
        sourceKPCompactChartPullback_of_positive K hζ F.val b y (hUp hyU)]
      exact hz
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
  have hpair (x : X) (hx : x ∈ U) :
      productGradientPair ψ.val.val g.val.val x = sourceKPCompactCorePairDensity K hζ F f (q x) := by
    have he := sourceKPCompactCorePairDensity_chart K hζ F f b (sourceKPArchEuclideanUpperMap K x)
    rw [sourceKPArchUpperEuclideanMap_right_inverse K x (fun i => productUpper_pos (hUp hx) i)] at he
    change sourceKPCompactCorePairDensity K hζ F f (q x) = productGradientPair Fcoord fcoord x at he
    rw [he]
    have hfd := (hFe hx).fderiv_eq (𝕜 := ℝ)
    by_cases hs : x ∈ tsupport ψ.val.val
    · have hg : g.val.val =ᶠ[𝓝 x] fcoord := by
        filter_upwards [hη x (hψ hs)] with y hy
        rw [sourceKPCompactCoreLocalized_apply, hy]
        simp only [Pi.one_apply, one_mul, fcoord]
      simp only [productGradientPair, productPartial, hfd, hg.fderiv_eq (𝕜 := ℝ)]
    · rw [fderiv_of_notMem_tsupport ℝ hs] at hfd
      simp only [productGradientPair, productPartial, hfd, fderiv_of_notMem_tsupport ℝ hs,
        ContinuousLinearMap.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, mul_zero]
  have hI : (∫ x, productGradientPair ψ.val.val g.val.val x ∂ν) =
      (Nat.card H : ℂ) * sourceKPCompactDirichletCore K hζ F f := by
    apply sourceKPFiniteChart_test_integral K hζ b p
      (sourceKPCompactCorePairDensity K hζ F f) _
      (sourceKPCompactCorePairDensity_continuous K hζ F f).measurable hpair
    · intro x hx
      have hs : x ∉ tsupport ψ.val.val := fun h => hx (ψ.prop h)
      simp only [productGradientPair, productPartial, fderiv_of_notMem_tsupport ℝ hs,
        ContinuousLinearMap.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, mul_zero]
    · intro y hy
      exact sourceKPCompactCorePairDensity_zero_outside_left K hζ F f
        (fun hs => hy (sourceKPChartPeriodizationCore_support K hζ b p φ hs))
  rw [← h1TestGradient_inner_integral] at hI
  change inner ℂ ((h1TestGradientLinear I) ((Fintype.card H : ℂ) • (A φ).val))
    (h1TestGradient g.val) = _ at hI
  rw [map_smul, inner_smul_left, map_natCast, Nat.card_eq_fintype_card] at hI
  change (Fintype.card H : ℂ) * inner ℂ (h1TestGradient (A φ).val) (h1TestGradient g.val) = _ at hI
  rw [sourceKPFiniteChartTestAverage_gradient_inner K hζ b p φ g
    (sourceKPCompactCoreLocalized_stabilizer K hζ b p η hηinv f)] at hI
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hI.symm

theorem sourceKPCompactH1Localization_dirichlet_periodized (η φ : Tests)
    (hηinv : ∀ (γ : H) (x : X), x ∈ Ω →
      η.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) = η.val.val x)
    {W : Set Y} (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1)
    (hφ : tsupport φ.val.val ⊆ V W) (u : SourceKPCompactH1 K hζ) :
    sourceKPCompactH1Dirichlet K hζ (sourceKPCompactH1Core K hζ ⟨P φ.val⟩) u =
      inner ℂ (h1TestGradient φ.val) (G (L η u)) := by
  let w := sourceKPCompactH1Core K hζ ⟨P φ.val⟩
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun v => sourceKPCompactH1Dirichlet K hζ w v =
      inner ℂ (h1TestGradient φ.val) (G (L η v))) u ?_ ?_
  · exact isClosed_eq (sourceKPCompactH1Dirichlet_continuous_right K hζ w)
      (continuous_const.inner ((G).continuous.comp (L η).continuous))
  · intro f
    change sourceKPCompactH1Dirichlet K hζ w (sourceKPCompactH1Core K hζ f) =
      inner ℂ (h1TestGradient φ.val) (G (L η (sourceKPCompactH1Core K hζ f)))
    rw [show w = sourceKPCompactH1Core K hζ ⟨P φ.val⟩ from rfl,
      sourceKPCompactH1Dirichlet_core, sourceKPCompactH1Localization_core, h1EnergyGradient_core]
    exact sourceKPCompactCoreLocalized_dirichlet_periodized K hζ b p η φ hηinv hη hφ f.val

end
end ArtinMatthews
