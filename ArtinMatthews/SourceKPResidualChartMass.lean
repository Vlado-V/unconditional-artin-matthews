module

public import ArtinMatthews.SourceKPResidualChartPlateau
public import ArtinMatthews.SourceKPCompactFormLocalization
public import ArtinMatthews.SourceKPChartPeriodizationCore
public import ArtinMatthews.L2MeasurableCutoff
public import ArtinMatthews.SourceKPCompactChartMassBound
public import ArtinMatthews.SourceKPCompactChartMassTest
public import ArtinMatthews.SourceKPCompactTruncatedChart
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

/-! The completed localized mass agrees with the actual residual pullback on the plateau. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "I" => InfinitePlace K
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "V" => sourceKPResidualChartPlateauDomain K hζ b p
local notation "q" => sourceKPCompactCoordinateProjection K hζ b
local notation "ν" => productVolume I
local notation "J" => sourceKPCompactH1Mass K hζ
local notation "L" => sourceKPCompactH1Localization K hζ b p
local notation "M" => h1EnergyMass I
local notation "B" => sourceKPCompactChartMassLiftCLM K hζ b p
local notation "Tests" => SourceKPFiniteChartTests K hζ b p

theorem sourceKPCompactH1Localization_mass_ae_plateau (η : Tests)
    {W : Set Y} (hW : IsOpen W) (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1)
    (u : SourceKPCompactH1 K hζ) :
    ∀ᵐ x ∂ν, x ∈ V W → M (L η u) x = J u (q x) := by
  let hV := (sourceKPResidualChartPlateauDomain_isOpen K hζ b p hW).measurableSet
  let C := measurableL2Cutoff ν (V W) hV
  let F := C.comp ((M).comp (L η))
  let G := C.comp ((B).comp J)
  have he : F u = G u := by
    refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
      (p := fun v => F v = G v) u (isClosed_eq F.continuous G.continuous) ?_
    intro f
    change C (M (L η (sourceKPCompactH1Core K hζ f))) =
      C (B (J (sourceKPCompactH1Core K hζ f)))
    rw [sourceKPCompactH1Localization_core, h1EnergyMass_core, sourceKPCompactH1Mass_core]
    let v := (sourceKPCompactCoreLocalized K hζ f.val b p η).val
    let g := sourceKPCompactCoreMass K hζ 2 f.val
    change C (h1TestMass v) = C (B g)
    apply Lp.ext
    filter_upwards [measurableL2Cutoff_coe ν (V W) hV (h1TestMass v),
      measurableL2Cutoff_coe ν (V W) hV (B g), h1TestMass_coe v,
      sourceKPCompactChartMassLiftCLM_coe K hζ b p g,
      sourceKPCompactCoordinateProjection_ae_chart K hζ b p
        (sourceKPCompactCoreMass_coe K hζ f.val)] with x hF hG hv hg hq
    rw [hF, hG]
    by_cases hx : x ∈ V W
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hv, hg,
        Set.indicator_of_mem hx.1]
      change v.val x = g (q x)
      rw [hq hx.1]
      change (sourceKPCompactCoreLocalized K hζ f.val b p η).val.val x = f.val.val (q x)
      rw [sourceKPCompactCoreLocalized_apply, (hη x hx).eq_of_nhds]
      change 1 * sourceKPCompactChartPullback K hζ f.val.val b x = f.val.val (q x)
      rw [one_mul]
      exact sourceKPCompactChartPullback_of_positive K hζ f.val.val b x
        (sourceKPFiniteChartCoordinateDomain_upper K hζ b p hx.1)
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  filter_upwards [measurableL2Cutoff_coe ν (V W) hV (M (L η u)),
    measurableL2Cutoff_coe ν (V W) hV (B (J u)),
    sourceKPCompactChartMassLiftCLM_coe K hζ b p (J u)] with x hF hG hB hx
  have hx' : x ∈ U := hx.1
  change C (M (L η u)) = C (B (J u)) at he
  rw [he, hG, Set.indicator_of_mem hx, hB, Set.indicator_of_mem hx'] at hF
  simpa only [Set.indicator_of_mem hx, Function.comp_apply] using hF.symm

theorem sourceKPCompactH1Localization_mass_inner_periodized (η φ : Tests)
    {W : Set Y} (hW : IsOpen W) (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1)
    (hφ : tsupport φ.val.val ⊆ V W) (u : SourceKPCompactH1 K hζ) :
    inner ℂ (h1TestMass φ.val) (M (L η u)) =
      inner ℂ (sourceKPCompactCoreMass K hζ 2
        (sourceKPChartPeriodizationCore K hζ b φ.val)) (J u) := by
  rw [← sourceKPCompactChartMassLift_inner K hζ b p φ (J u)]
  change inner ℂ (h1TestMass φ.val) (M (L η u)) =
    inner ℂ (h1TestMass φ.val) (B (J u))
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h1TestMass_coe φ.val, sourceKPCompactChartMassLiftCLM_coe K hζ b p (J u),
    sourceKPCompactH1Localization_mass_ae_plateau K hζ b p η hW hη u] with x hφx hB hM
  rw [hφx]
  by_cases hx : x ∈ V W
  · rw [hM hx, hB, Set.indicator_of_mem hx.1]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hφ hs)), inner_zero_left, inner_zero_left]

end
end ArtinMatthews
