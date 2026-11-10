module

public import ArtinMatthews.SourceKPAdelicOutgoingSection
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

/-! Every actual outgoing coordinate is the corresponding left-torus
translate of the literal scalar trace integral, with its fixed half
modular scalar. This gives an exact interface for scalar continuation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "O" => sourceKPAdelicOutgoingSection K hζ
local notation "I" => sourceKPAdelicTraceIntertwiner K hζ
local notation "d₀" => sourceKPAdelicBorelTorusInclusion K hζ
local notation "δ" => sourceKPAdelicBorelModularHalf K hζ

theorem sourceKPAdelicOutgoingSection_trace_coordinate (s : ℂ) (g : G) (t : T) :
    ((O s).val g).val t = (δ (d₀ t))⁻¹ * I s (t.val*g) := by
  have h := congrArg (fun v : V (-s) => v.val 1)
    ((O s).property (d₀ t) g)
  change ((O s).val (t.val*g)).val 1 =
    δ (d₀ t)*((O s).val g).val (1*sourceKPAdelicBorelTorusProjection K hζ (d₀ t)) at h
  rw [sourceKPAdelicBorelTorusProjection_inclusion,one_mul,
    sourceKPAdelicOutgoingSection_trace_one K hζ] at h
  have hn : δ (d₀ t) ≠ 0 := by
    change (sourceKPIdeleComplexNorm K (1/2 : ℂ)
      (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ (d₀ t))) : ℂ) ≠ 0
    exact Units.ne_zero _
  rw [h,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

end
end ArtinMatthews
