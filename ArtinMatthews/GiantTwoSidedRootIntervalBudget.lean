module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The literal ceiling interval has a positive lower endpoint and
enough integer roots for the relative CRT estimate. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem giantTwoSidedRootInterval_lower_endpoint {X : ℝ} (hX : 0<X) : 1≤⌈X⌉₊ :=
  Nat.ceil_pos.mpr hX

theorem giantTwoSidedRootInterval_length {X : ℝ} (hX : 2≤X) :
    X/2≤((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ) := by
  have hX0 : 0≤X := zero_le_two.trans hX
  have hc : ⌈X⌉₊≤⌈2*X⌉₊ := Nat.ceil_mono (by linarith)
  rw [Nat.cast_sub hc]
  have hlo := Nat.le_ceil (2*X)
  have hhi := (Nat.ceil_lt_add_one hX0).le
  linarith

theorem giantCandidateRootInterval_budget {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,∀ X : ℝ,x^γ≤X →
      1≤⌈X⌉₊ ∧ Real.exp ((γ/2)*Real.log x)≤((⌈2*X⌉₊-⌈X⌉₊:ℕ):ℝ) := by
  have hγ2 : 0<γ/2 := half_pos hγ
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop hγ2).eventually_ge_atTop (2:ℝ)] with x hx hlarge
  intro X hX
  have hpow : x^γ=(x^(γ/2))^2 := by
    rw [sq,← Real.rpow_add hx]
    congr 1
    ring
  have hX2 : 2≤X := by rw [hpow] at hX; nlinarith
  have hmid : x^(γ/2)≤X/2 := by
    rw [hpow] at hX
    have hmul := mul_le_mul_of_nonneg_right hlarge (zero_le_two.trans hlarge)
    nlinarith only [hX,hmul]
  refine ⟨giantTwoSidedRootInterval_lower_endpoint (zero_lt_two.trans_le hX2),?_⟩
  have he : Real.exp ((γ/2)*Real.log x)=x^(γ/2) := by
    rw [Real.rpow_def_of_pos hx,mul_comm]
  rw [he]
  exact hmid.trans (giantTwoSidedRootInterval_length hX2)

end
end ArtinMatthews
