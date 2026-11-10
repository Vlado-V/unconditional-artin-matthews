module

public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.SourceKPCompactGenuineL2
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

/-! The genuine subspace of the actual completed compact-quotient form. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "V" => SourceKPCompactH1 K hζ
local notation "L" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "G" => sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactGenuineH1 : Submodule ℂ V :=
  (G).comap (sourceKPCompactH1Mass K hζ).toLinearMap

abbrev SourceKPCompactGenuineH1 := ↥(sourceKPCompactGenuineH1 K hζ)

theorem sourceKPCompactGenuineH1_isClosed :
    IsClosed (sourceKPCompactGenuineH1 K hζ : Set V) :=
  (sourceKPCompactGenuineL2Subspace_isClosed K hζ (sourceKPArchHaar K hζ)).preimage
    (sourceKPCompactH1Mass K hζ).continuous

instance sourceKPCompactGenuineH1_complete : CompleteSpace (SourceKPCompactGenuineH1 K hζ) :=
  (sourceKPCompactGenuineH1_isClosed K hζ).completeSpace_coe

def sourceKPCompactGenuineH1Mass :
    SourceKPCompactGenuineH1 K hζ →L[ℂ] SourceKPGenuineAutomorphicL2 K hζ :=
  ((sourceKPCompactH1Mass K hζ).comp (sourceKPCompactGenuineH1 K hζ).subtypeL).codRestrict
    G (fun u => u.prop)

theorem sourceKPCompactGenuineH1Mass_coe (u : SourceKPCompactGenuineH1 K hζ) :
    (sourceKPCompactGenuineH1Mass K hζ u : L) = sourceKPCompactH1Mass K hζ u.val :=
  rfl

theorem sourceKPCompactGenuineH1Mass_norm_le (u : SourceKPCompactGenuineH1 K hζ) :
    ‖sourceKPCompactGenuineH1Mass K hζ u‖ ≤ ‖u‖ :=
  sourceKPCompactH1Mass_norm_le K hζ u.val

theorem sourceKPCompactGenuineH1Dirichlet_self (u : SourceKPCompactGenuineH1 K hζ) :
    (sourceKPCompactH1Dirichlet K hζ u.val u.val).re =
      ‖u‖ ^ 2 - ‖sourceKPCompactGenuineH1Mass K hζ u‖ ^ 2 :=
  sourceKPCompactH1Dirichlet_self K hζ u.val

end
end ArtinMatthews
