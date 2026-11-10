module

public import ArtinMatthews.SourceKPCompactSetMassPairing
public import ArtinMatthews.L2MeasurableCutoff
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

/-! Compact native tests use their actual image in the compact automorphic quotient. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter Set
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)
local notation "q" => sourceKPCompactCoordinateProjection K hζ b

theorem sourceKPCompactCoordinateProjection_continuousOn :
    ContinuousOn q (productUpper (InfinitePlace K)) :=
  (sourceKPUpperToCompact_continuous K hζ b).comp_continuousOn
    (sourceKPArchEuclideanUpperMap_continuousOn K)

def sourceKPCompactNativeTestImage (S : Set X) : Set Y := q '' S

theorem sourceKPCompactNativeTestImage_isCompact (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) :
    IsCompact (sourceKPCompactNativeTestImage K hζ b S) :=
  hS.image_of_continuousOn ((sourceKPCompactCoordinateProjection_continuousOn K hζ b).mono hSu)

theorem sourceKPCompactNativeTestImage_mem (S : Set X) {x : X} (hx : x ∈ S) :
    q x ∈ sourceKPCompactNativeTestImage K hζ b S := ⟨x, hx, rfl⟩

theorem sourceKPCompactSetMassPairing_cutoff (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C)
    (Q : Set Y) (hQ : MeasurableSet Q) (himage : q '' S ⊆ Q) (g : Lp ℂ 2 μ) :
    sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC (measurableL2Cutoff μ Q hQ g) =
      sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC g := by
  rw [sourceKPCompactSetMassPairing_apply_of_ae K hζ b S hS hSu φ hφ C hC
      (measurableL2Cutoff μ Q hQ g) (measurableL2Cutoff_coe μ Q hQ g),
    sourceKPCompactSetMassPairing_apply K hζ b S hS hSu φ hφ C hC g]
  apply setIntegral_congr_fun hS.measurableSet
  intro x hx
  dsimp only
  rw [Set.indicator_of_mem (himage ⟨x, hx, rfl⟩)]

end
end ArtinMatthews
