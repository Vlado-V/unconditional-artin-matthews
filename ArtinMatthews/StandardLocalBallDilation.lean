module

public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.StandardLocalFourier
public import ArtinMatthews.StandardLocalHaarScaling
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Actual arbitrary local dilations shift the integer valuation radius
by the logarithm of the literal valuation. The Haar factor is exactly
the normalized Mathlib finite-place absolute value. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

theorem sourceLocalNorm_eq_zpow (x : P.adicCompletion K) (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm P.asIdeal : ℝ) ^ WithZero.log (sourceLocalValuation K P x) := by
  have hv : sourceLocalValuation K P x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  simp only [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply
    (NumberField.HeightOneSpectrum.absNorm_ne_zero P) hv, NNReal.coe_zpow, NNReal.coe_natCast]

theorem sourceLocalBall_div_mem (n : ℤ) (t : (P.adicCompletion K)ˣ) (x : P.adicCompletion K) :
    x / (t : P.adicCompletion K) ∈ sourceLocalBall K P n ↔
      x ∈ sourceLocalBall K P (n + WithZero.log (sourceLocalValuation K P (t : P.adicCompletion K))) := by
  let v := sourceLocalValuation K P
  have hv : v (t : P.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  change v (x / (t : P.adicCompletion K)) ≤ WithZero.exp n ↔
    v x ≤ WithZero.exp (n + WithZero.log (v (t : P.adicCompletion K)))
  rw [map_div₀, div_le_iff₀ (pos_iff_ne_zero.mpr hv), WithZero.exp_add, WithZero.exp_log hv]

theorem sourceLocalBall_dilation_volume (μ : Measure (P.adicCompletion K)) [μ.IsAddHaarMeasure]
    (n : ℤ) (t : (P.adicCompletion K)ˣ) :
    μ.real (sourceLocalBall K P (n + WithZero.log (sourceLocalValuation K P (t : P.adicCompletion K)))) =
      ‖(t : P.adicCompletion K)‖ * μ.real (sourceLocalBall K P n) := by
  rw [sourceLocalBall_volume_scaling K P μ, sourceLocalBall_volume_scaling K P μ n,
    sourceLocalNorm_eq_zpow K P (t : P.adicCompletion K) t.ne_zero,
    zpow_add₀ (sourceLocalNorm_pos K P).ne']
  ring

end
end ArtinMatthews.SourcePhysical
