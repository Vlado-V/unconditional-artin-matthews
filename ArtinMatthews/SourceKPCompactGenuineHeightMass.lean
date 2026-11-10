module

public import ArtinMatthews.SourceKPCompactGenuineH1
public import ArtinMatthews.SourceKPCompactHeightMass
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

/-! The same literal sublevel restriction on the actual genuine form space. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "Vχ" => SourceKPCompactGenuineH1 K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L" => Lp ℂ 2 μ
local notation "S" => (fun R : ℝ => Set.ofPred (fun y : Y => sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ R))

def sourceKPCompactGenuineH1LocalizedMass (R : ℝ) : Vχ →L[ℂ] L :=
  (sourceKPCompactH1LocalizedMass K hζ R).comp (sourceKPCompactGenuineH1 K hζ).subtypeL

theorem sourceKPCompactGenuineH1LocalizedMass_apply (R : ℝ) (u : Vχ) :
    sourceKPCompactGenuineH1LocalizedMass K hζ R u =
      sourceKPCompactHeightCutoff K hζ R (sourceKPCompactGenuineH1Mass K hζ u : L) :=
  rfl

theorem sourceKPCompactGenuineH1LocalizedMass_coe (R : ℝ) (u : Vχ) :
    (sourceKPCompactGenuineH1LocalizedMass K hζ R u : Y → ℂ) =ᵐ[μ]
      (S R).indicator (sourceKPCompactGenuineH1Mass K hζ u : L) :=
  sourceKPCompactH1LocalizedMass_coe K hζ R u.val

theorem sourceKPCompactGenuineH1LocalizedMass_norm_sq (R : ℝ) (u : Vχ) :
    ‖sourceKPCompactGenuineH1LocalizedMass K hζ R u‖ ^ 2 =
      ∫ y in S R, ‖(sourceKPCompactGenuineH1Mass K hζ u : L) y‖ ^ 2 ∂μ :=
  sourceKPCompactH1LocalizedMass_norm_sq K hζ R u.val

end
end ArtinMatthews
