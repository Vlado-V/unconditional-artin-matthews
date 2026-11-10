module

public import ArtinMatthews.SourceKPCompactH1GenuineProjection
public import ArtinMatthews.SourceKPCompactH1ClosedForm
public import ArtinMatthews.SourceKPCompactH1Injective
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

/-! The genuine completed form has a dense embedded mass and the literal cubic core. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactGenuineH1Mass_injective :
    Function.Injective (sourceKPCompactGenuineH1Mass K hζ) :=
  sourceKPCompactGenuineH1Mass_injective_of K hζ (sourceKPCompactH1Mass_injective K hζ)

theorem sourceKPCompactGenuineH1Mass_denseRange :
    DenseRange (sourceKPCompactGenuineH1Mass K hζ) :=
  sourceKPCompactGenuineH1Mass_denseRange_of K hζ (sourceKPCompactH1Mass_denseRange K hζ)

theorem sourceKPCompactGenuineH1Mass_opNorm_le : ‖sourceKPCompactGenuineH1Mass K hζ‖ ≤ 1 :=
  (sourceKPCompactGenuineH1Mass K hζ).opNorm_le_bound zero_le_one (fun u => by
    simpa only [one_mul] using sourceKPCompactGenuineH1Mass_norm_le K hζ u)

theorem sourceKPCompactGenuineH1ProjectedCore_hasDenseRange :
    DenseRange (sourceKPCompactGenuineH1ProjectedCore K hζ) :=
  sourceKPCompactGenuineH1ProjectedCore_denseRange K hζ (sourceKPCompactH1Mass_injective K hζ)

theorem sourceKPCompactH1Projector_range :
    (sourceKPCompactH1Projector K hζ).range = sourceKPCompactGenuineH1 K hζ := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact sourceKPCompactH1Projector_mem_genuine K hζ v
  · intro hu
    obtain ⟨v, hv⟩ := sourceKPCompactH1ProjectToGenuine_surjective K hζ
      (sourceKPCompactH1Mass_injective K hζ) ⟨u, hu⟩
    exact ⟨v, congrArg Subtype.val hv⟩

end
end ArtinMatthews
