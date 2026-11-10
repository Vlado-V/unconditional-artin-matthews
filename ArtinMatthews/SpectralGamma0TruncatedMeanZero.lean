module

public import ArtinMatthews.SpectralCuspConstantTermOperator
public import ArtinMatthews.SpectralCuspConstantTermHeights
public import ArtinMatthews.SpectralCuspProjectedConstant
public import ArtinMatthews.SpectralGamma0CuspCompletedGraph
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! A genuine closed truncated constant-mode energy form. Constant modes
are required to vanish only above one fixed cutoff, rather than at every
positive height. Actual residual-tail estimates prove its mass escape. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0TruncatedMeanZeroEnergy (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) :
    Submodule ℂ (gamma0EnergySpace N) :=
  ⨅ r : SL(2,ℤ), ((gamma0CuspConstantTerm N r A hA).comp (gamma0EnergyInclusion N)).ker

theorem mem_gamma0TruncatedMeanZeroEnergy_iff (N : ℕ) [NeZero N]
    (A : ℝ) (hA : 0<A) (u : gamma0EnergySpace N) :
    u ∈ gamma0TruncatedMeanZeroEnergy N A hA ↔
      ∀ r : SL(2,ℤ), gamma0CuspConstantTerm N r A hA (gamma0EnergyInclusion N u)=0 := by
  simp only [gamma0TruncatedMeanZeroEnergy,Submodule.mem_iInf,LinearMap.mem_ker]
  rfl

theorem gamma0TruncatedMeanZeroEnergy_isClosed (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) :
    IsClosed (gamma0TruncatedMeanZeroEnergy N A hA : Set (gamma0EnergySpace N)) := by
  unfold gamma0TruncatedMeanZeroEnergy
  simp_rw [Submodule.coe_iInf]
  exact isClosed_iInter fun _ => ContinuousLinearMap.isClosed_ker _

instance gamma0TruncatedMeanZeroEnergy_complete (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) :
    CompleteSpace (gamma0TruncatedMeanZeroEnergy N A hA) :=
  (gamma0TruncatedMeanZeroEnergy_isClosed N A hA).isComplete.completeSpace_coe

theorem gamma0TruncatedMeanZeroEnergy_constantTerm_zero (N : ℕ) [NeZero N]
    (A : ℝ) (hA : 0<A) (u : gamma0TruncatedMeanZeroEnergy N A hA)
    (r : SL(2,ℤ)) {Y : ℝ} (hAY : A≤Y) :
    gamma0CuspConstantTerm N r Y (hA.trans_le hAY) (gamma0EnergyInclusion N u.val)=0 := by
  have hc := (mem_gamma0TruncatedMeanZeroEnergy_iff N A hA u.val).mp u.property r
  rw [← gamma0CuspConstantTerm_height_restriction N r A Y hA (hA.trans_le hAY) hAY,
    hc,map_zero]

theorem gamma0TruncatedMeanZeroEnergy_tail_bound (N : ℕ) [NeZero N]
    (A : ℝ) (hA : 0<A) (u : gamma0TruncatedMeanZeroEnergy N A hA)
    (r : SL(2,ℤ)) {Y : ℝ} (hY : 1≤Y) (hAY : A≤Y) :
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (gamma0CuspEnergyRestriction N r u.val)‖^2 ≤
      ((N:ℝ)^2/Y^2)*(((N:ℝ)+1)*‖u‖^2) := by
  have hz := gamma0CuspEnergyProjection_restricted_zero N r u.val hY
    (gamma0TruncatedMeanZeroEnergy_constantTerm_zero N A hA u r hAY)
  have ht := gamma0CuspEnergy_residual_tail_bound N r u.val hY
  rw [map_sub,hz,sub_zero] at ht
  exact ht

end ArtinMatthews
