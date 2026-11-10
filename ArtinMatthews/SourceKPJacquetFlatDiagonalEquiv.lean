module

public import ArtinMatthews.SourceKPJacquetFlatDiagonal
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

/-! The normalized actual diagonal is an invertible linear action. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
local notation "L" => P.adicCompletion K

def sourceKPJacquetFlatDiagonalEquiv (u : Lˣ) : V ≃ₗ[ℂ] V := by
  let b := sourceFiniteKPProjectiveBorelDiagonal K hζ P u
  let E : V ≃ₗ[ℂ] V := LinearEquiv.ofLinearMap (ρ b) (ρ b⁻¹)
    (by
      change ρ b * ρ b⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one])
    (by
      change ρ b⁻¹ * ρ b = 1
      rw [← map_mul, inv_mul_cancel, map_one])
  let c : ℂ := (↑(‖(u : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr u.ne_zero) _).ne'
  exact E.trans (LinearEquiv.smulOfNeZero ℂ V c hc)

theorem sourceKPJacquetFlatDiagonalEquiv_apply (u : Lˣ) (v : V) :
    sourceKPJacquetFlatDiagonalEquiv K hζ P ρ u v = sourceKPJacquetFlatDiagonal K hζ P ρ u v := rfl

end
end ArtinMatthews
