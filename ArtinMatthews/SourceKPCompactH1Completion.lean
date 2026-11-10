module

public import ArtinMatthews.SourceKPCompactFormCoreNorm
public import Mathlib.Analysis.InnerProductSpace.Completion
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

/-! Complete mass-and-energy space of the literal compact-cover test core. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen UniformSpace
open scoped NumberField MatrixGroups AdeleRing Topology InnerProductSpace ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "T" => SourceKPCompactFormCore K hζ
local notation "L" => Lp ℂ 2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ))
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

abbrev SourceKPCompactH1 := Completion T

def sourceKPCompactH1Core : T →ₗᵢ[ℂ] SourceKPCompactH1 K hζ := Completion.toComplₗᵢ

def sourceKPCompactH1Mass : SourceKPCompactH1 K hζ →L[ℂ] L :=
  (sourceKPCompactFormCoreMass K hζ).fromCompletion

theorem sourceKPCompactH1Mass_core (f : T) :
    sourceKPCompactH1Mass K hζ (sourceKPCompactH1Core K hζ f) =
      sourceKPCompactFormCoreMassLinear K hζ f :=
  (sourceKPCompactFormCoreMass K hζ).fromCompletion_apply_coe f

theorem sourceKPCompactH1Core_denseRange : DenseRange (sourceKPCompactH1Core K hζ) :=
  Completion.denseRange_coe

theorem sourceKPCompactH1Mass_norm_le (f : SourceKPCompactH1 K hζ) :
    ‖sourceKPCompactH1Mass K hζ f‖ ≤ ‖f‖ := by
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun u => ‖sourceKPCompactH1Mass K hζ u‖ ≤ ‖u‖) f ?_ ?_
  · exact isClosed_le ((sourceKPCompactH1Mass K hζ).continuous.norm) continuous_norm
  · intro g
    simpa only [sourceKPCompactH1Mass_core,LinearIsometry.norm_map] using
      sourceKPCompactFormCoreMassLinear_norm_le K hζ g

def sourceKPCompactH1Dirichlet (f g : SourceKPCompactH1 K hζ) : ℂ :=
  inner ℂ f g - inner ℂ (sourceKPCompactH1Mass K hζ f) (sourceKPCompactH1Mass K hζ g)

theorem sourceKPCompactH1Dirichlet_core (f g : T) :
    sourceKPCompactH1Dirichlet K hζ (sourceKPCompactH1Core K hζ f) (sourceKPCompactH1Core K hζ g) =
      sourceKPCompactDirichletCore K hζ f.val g.val := by
  unfold sourceKPCompactH1Dirichlet
  rw [LinearIsometry.inner_map_map,sourceKPCompactH1Mass_core,sourceKPCompactH1Mass_core]
  change sourceKPCompactFormCoreInner K hζ f g - _ = _
  unfold sourceKPCompactFormCoreInner
  abel

theorem sourceKPCompactH1Dirichlet_self (f : SourceKPCompactH1 K hζ) :
    (sourceKPCompactH1Dirichlet K hζ f f).re = ‖f‖ ^ 2 - ‖sourceKPCompactH1Mass K hζ f‖ ^ 2 := by
  unfold sourceKPCompactH1Dirichlet
  rw [Complex.sub_re]
  exact congrArg₂ (· - ·) (inner_self_eq_norm_sq (𝕜 := ℂ) f)
    (inner_self_eq_norm_sq (𝕜 := ℂ) (sourceKPCompactH1Mass K hζ f))

theorem sourceKPCompactH1Dirichlet_nonneg (f : SourceKPCompactH1 K hζ) :
    0 ≤ (sourceKPCompactH1Dirichlet K hζ f f).re := by
  rw [sourceKPCompactH1Dirichlet_self]
  exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (sourceKPCompactH1Mass_norm_le K hζ f) 2)

end
end ArtinMatthews
