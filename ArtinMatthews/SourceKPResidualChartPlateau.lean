module

public import ArtinMatthews.SourceKPCompactChartMassLift
public import ArtinMatthews.SourceKPCompactCoreLocalization
public import ArtinMatthews.SourceKPCompactChartPlateau
public import ArtinMatthews.SourceKPCompactEnergyRegularity
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
public import Mathlib.NumberTheory.Height.NumberField
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

/-! An invariant cutoff for a neighborhood inside each actual arithmetic chart. -/

namespace ArtinMatthews
open NumberField Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "Ω" => productUpper (InfinitePlace K)
local notation "q" => sourceKPCompactCoordinateProjection K hζ b
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "Tests" => SourceKPFiniteChartTests K hζ b p

def sourceKPResidualChartPlateauDomain (W : Set Y) : Set X :=
  U ∩ q ⁻¹' W

local notation "V" => sourceKPResidualChartPlateauDomain K hζ b p

theorem sourceKPCompactCoordinateProjection_continuousOn :
    ContinuousOn q Ω :=
  (sourceKPUpperToCompact_continuous K hζ b).comp_continuousOn
    (sourceKPArchEuclideanUpperMap_continuousOn K)

theorem sourceKPCompactCoordinateProjection_stabilizer (γ : H) (x : X) :
    q (sourceKPArchEuclideanAction K hζ γ.val.val x) = q x := by
  unfold sourceKPCompactCoordinateProjection sourceKPArchEuclideanAction
  rw [sourceKPArchUpperEuclideanMap_left_inverse]
  exact sourceKPUpperToCompact_smul K hζ b γ.val _

theorem sourceKPResidualChartPlateauDomain_isOpen {W : Set Y} (hW : IsOpen W) :
    IsOpen (V W) :=
  ((sourceKPCompactCoordinateProjection_continuousOn K hζ b).mono
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)).isOpen_inter_preimage
    (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p) hW

theorem sourceKPResidualChartPlateauDomain_center {W : Set Y}
    (hW : sourceKPUpperToCompact K hζ b p ∈ W) :
    sourceKPArchUpperEuclideanMap K p ∈ V W := by
  refine ⟨sourceKPFiniteChartCoordinateDomain_mem K hζ b p, ?_⟩
  simpa only [sourceKPCompactCoordinateProjection, Set.mem_preimage,
    sourceKPArchUpperEuclideanMap_left_inverse] using hW

theorem sourceKPResidualChartPlateau_exists :
    ∃ (η : Tests) (W : Set Y),
      IsOpen W ∧ sourceKPUpperToCompact K hζ b p ∈ W ∧
      (∀ (γ : H) (x : X), x ∈ Ω →
        η.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) = η.val.val x) ∧
      ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1 := by
  obtain ⟨η, W, hW, hp, _, hη⟩ := sourceKPCompactChartPlateau_exists K hζ b p
  refine ⟨sourceKPFiniteChartTestAverage K hζ b p η, W, hW, hp,
    sourceKPFiniteChartTestAverage_invariant K hζ b p η, ?_⟩
  intro x hx
  filter_upwards [(sourceKPResidualChartPlateauDomain_isOpen K hζ b p hW).mem_nhds hx] with y hy
  rw [sourceKPFiniteChartTestAverage_apply K hζ b p η y
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p hy.1)]
  have he (γ : H) : η.val.val (sourceKPArchEuclideanAction K hζ γ.val.val y) = 1 :=
    (hη _ (sourceKPFiniteChartCoordinateDomain_invariant K hζ b p γ hy.1)
      (sourceKPCompactCoordinateProjection_stabilizer K hζ b p γ y ▸ hy.2)).eq_of_nhds
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]
  rfl

theorem sourceKPResidualChartPlateauDomain_support (η : Tests) (W : Set Y)
    (hη : ∀ x ∈ V W, η.val.val =ᶠ[𝓝 x] 1) :
    V W ⊆ tsupport η.val.val := by
  intro x hx
  apply subset_tsupport
  change η.val.val x ≠ 0
  rw [(hη x hx).eq_of_nhds]
  exact one_ne_zero

theorem sourceKPCompactCoreLocalized_stabilizer (η : Tests)
    (hη : ∀ (γ : H) (x : X), x ∈ Ω →
      η.val.val (sourceKPArchEuclideanAction K hζ γ.val.val x) = η.val.val x)
    (f : sourceKPCompactC2Core K hζ) (γ : H) :
    sourceKPFiniteChartTestPullback K hζ b p γ
        (sourceKPCompactCoreLocalized K hζ f b p η) =
      sourceKPCompactCoreLocalized K hζ f b p η := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Ω
  · rw [sourceKPFiniteChartTestPullback_apply K hζ b p γ _ x hx,
      sourceKPCompactCoreLocalized_apply, sourceKPCompactCoreLocalized_apply,
      hη γ x hx, sourceKPCompactChartPullback_invariant K hζ f.val b γ.val x hx]
  · let g := sourceKPCompactCoreLocalized K hζ f b p η
    change sourceKPArchTestPullbackFun K hζ γ.val.val g.val x = g.val.val x
    rw [sourceKPArchTestPullbackFun, if_neg hx]
    exact (image_eq_zero_of_notMem_tsupport (fun hs => hx (g.val.prop.2.2 hs))).symm

end
end ArtinMatthews
