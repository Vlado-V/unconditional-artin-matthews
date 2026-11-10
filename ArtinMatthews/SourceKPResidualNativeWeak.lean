module

public import ArtinMatthews.SourceKPAutomorphicSpectralContinuation
public import ArtinMatthews.SourceKPCompactFormLocalization
public import ArtinMatthews.SourceKPResidualChartPlateau
public import ArtinMatthews.SourceKPCompactTruncatedChart
public import ArtinMatthews.SourceKPResidualChartDirichlet
public import ArtinMatthews.SourceKPResidualChartMass
public import ArtinMatthews.SourceKPResidualScalarWeak
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

/-! The actual exceptional residue satisfies the native weak eigen-equation in every finite-level chart. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen HilbertResolvent
open scoped NumberField MatrixGroups AdeleRing Topology Classical InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "I" => InfinitePlace K
local notation "X" => ProductSpace I
local notation "Ω" => productUpper I
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "V" => sourceKPResidualChartPlateauDomain K hζ b p
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "ν" => productVolume I
local notation "J" => sourceKPCompactH1Mass K hζ
local notation "L" => sourceKPCompactH1Localization K hζ b p
local notation "M" => h1EnergyMass I
local notation "G" => h1EnergyGradient I
local notation "Tests" => SourceKPFiniteChartTests K hζ b p
local notation "λR" => (exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ) : ℂ)
local notation "Rform" => sourceKPAutomorphicExceptionalFormResidue K hζ
local notation "Rmass" => sourceKPAutomorphicExceptionalResidue K hζ

theorem sourceKPResidualLocalizedMass_ae_plateau {T : ℝ} (hT : 1 ≤ T) (η : Tests)
    {W : Set Y} (hW : IsOpen W) (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1) :
    ∀ᵐ x ∂ν, x ∈ V W → M (L η (Rform hT).val) x =
      sourceKPCompactChartPullback K hζ ((Rmass hT).val : Y → ℂ) b x := by
  have hm : J (Rform hT).val = (Rmass hT).val := congrArg Subtype.val
    (sourceKPAutomorphicExceptionalFormResidue_mass K hζ hT)
  filter_upwards [sourceKPCompactH1Localization_mass_ae_plateau K hζ b p η hW hη
    (Rform hT).val] with x hx hxV
  rw [hx hxV, hm, sourceKPCompactChartPullback_of_positive K hζ _ b x
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p hxV.1)]
  rfl

theorem sourceKPResidualLocalized_weak_eigen {T : ℝ} (hT : 1 ≤ T) (η : Tests)
    (hηinv : ∀ (γ : H) (x : X), x ∈ Ω →
      η.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) = η.val.val x)
    {W : Set Y} (hW : IsOpen W) (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1)
    (φ : h1Tests I 2) (hφ : tsupport φ.val ⊆ V W) :
    inner ℂ (h1TestGradient φ) (G (L η (Rform hT).val)) =
      λR * inner ℂ (h1TestMass φ) (M (L η (Rform hT).val)) := by
  let φ' : Tests := ⟨φ, hφ.trans Set.inter_subset_left⟩
  let F := sourceKPChartPeriodizationCore K hζ b φ
  let v := sourceKPCompactH1Core K hζ ⟨F⟩
  have hm : J (Rform hT).val = (Rmass hT).val := congrArg Subtype.val
    (sourceKPAutomorphicExceptionalFormResidue_mass K hζ hT)
  have h := sourceKPAutomorphicExceptionalFormResidue_weak_eigen_scalar K hζ hT v
  rw [sourceKPCompactH1Localization_dirichlet_periodized K hζ b p η φ' hηinv hη hφ,
    sourceKPCompactH1Mass_core, ← hm] at h
  change inner ℂ (h1TestGradient φ) (G (L η (Rform hT).val)) =
    λR * inner ℂ (sourceKPCompactCoreMass K hζ 2 F) (J (Rform hT).val) at h
  rw [← sourceKPCompactH1Localization_mass_inner_periodized K hζ b p η φ' hW hη hφ] at h
  exact h

theorem sourceKPResidualLocalized_weak_eigen_exists {T : ℝ} (hT : 1 ≤ T) :
    ∃ (η : Tests) (W : Set Y),
      IsOpen W ∧ sourceKPUpperToCompact K hζ b p ∈ W ∧
      (∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1) ∧
      (∀ᵐ x ∂ν, x ∈ V W → M (L η (Rform hT).val) x =
        sourceKPCompactChartPullback K hζ ((Rmass hT).val : Y → ℂ) b x) ∧
      ∀ (φ : h1Tests I 2), tsupport φ.val ⊆ V W →
        inner ℂ (h1TestGradient φ) (G (L η (Rform hT).val)) =
          λR * inner ℂ (h1TestMass φ) (M (L η (Rform hT).val)) := by
  obtain ⟨η, W, hW, hp, hηinv, hη⟩ := sourceKPResidualChartPlateau_exists K hζ b p
  exact ⟨η, W, hW, hp, hη, sourceKPResidualLocalizedMass_ae_plateau K hζ b p hT η hW hη,
    sourceKPResidualLocalized_weak_eigen K hζ b p hT η hηinv hW hη⟩

theorem sourceKPCompactH1Localization_core_seq (η : Tests) (u : SourceKPCompactH1 K hζ) :
    ∃ f : ℕ → h1Tests I 2,
      (∀ n, tsupport (f n).val ⊆ tsupport η.val.val) ∧
      Tendsto (fun n => h1TestMass (f n)) atTop (𝓝 (M (L η u))) ∧
      Tendsto (fun n => h1TestGradient (f n)) atTop (𝓝 (G (L η u))) := by
  obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp
    ((sourceKPCompactH1Core_denseRange K hζ) u)
  choose a ha using hs
  have ha' : Tendsto (fun n => sourceKPCompactH1Core K hζ (a n)) atTop (𝓝 u) := by
    simpa only [ha] using ht
  let f := fun n => (sourceKPCompactCoreLocalized K hζ (a n).val b p η).val
  have hsupp (n : ℕ) : tsupport (f n).val ⊆ tsupport η.val.val := by
    change tsupport (fun x => η.val.val x * sourceKPCompactChartPullback K hζ (a n).val.val b x) ⊆ _
    exact tsupport_mul_subset_left
  have hL : Tendsto (fun n => h1EnergyCore (f n)) atTop (𝓝 (L η u)) := by
    have h := ((L η).continuous.tendsto u).comp ha'
    change Tendsto (fun n => L η (sourceKPCompactH1Core K hζ (a n))) atTop (𝓝 (L η u)) at h
    simpa only [sourceKPCompactH1Localization_core, f] using h
  exact ⟨f, hsupp,
    ((M).continuous.tendsto _).comp hL,
    ((G).continuous.tendsto _).comp hL⟩

end
end ArtinMatthews
