module

public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.SourceKPCompactCoreDensity
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

/-! The actual densely defined closed scalar Dirichlet form on compact automorphic level. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology InnerProductSpace ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "V" => SourceKPCompactH1 K hζ

theorem sourceKPCompactH1Mass_denseRange : DenseRange (sourceKPCompactH1Mass K hζ) :=
  (sourceKPCompactCoreMass_denseRange K hζ).mono (by
    rintro y ⟨f,rfl⟩
    exact ⟨sourceKPCompactH1Core K hζ ⟨f⟩,sourceKPCompactH1Mass_core K hζ ⟨f⟩⟩)

def sourceKPCompactH1DirichletRight (f : V) : V →L[ℂ] ℂ :=
  innerSL ℂ f - (innerSL ℂ (sourceKPCompactH1Mass K hζ f)).comp (sourceKPCompactH1Mass K hζ)

theorem sourceKPCompactH1DirichletRight_apply (f g : V) :
    sourceKPCompactH1DirichletRight K hζ f g = sourceKPCompactH1Dirichlet K hζ f g := rfl

theorem sourceKPCompactH1Dirichlet_conj_symm (f g : V) :
    conj (sourceKPCompactH1Dirichlet K hζ f g) = sourceKPCompactH1Dirichlet K hζ g f := by
  simp only [sourceKPCompactH1Dirichlet,map_sub,inner_conj_symm]

theorem sourceKPCompactH1_norm_sq (f : V) :
    ‖f‖ ^ 2 = ‖sourceKPCompactH1Mass K hζ f‖ ^ 2 + (sourceKPCompactH1Dirichlet K hζ f f).re := by
  rw [sourceKPCompactH1Dirichlet_self]
  ring

end
end ArtinMatthews
