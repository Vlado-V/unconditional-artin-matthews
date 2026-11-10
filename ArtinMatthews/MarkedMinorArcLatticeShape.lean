module

public import ArtinMatthews.MarkedMinorArcLatticeCoordinates
public import ArtinMatthews.MarkedMinorArcOperator
public import ArtinMatthews.MarkedMinorArcLatticeBox
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

/-! Full source lattice-box exponents, retaining the .1 lower side bounds
and .9 upper side bounds after absorbing fixed geometry constants. -/
namespace ArtinMatthews

/-- Fixed geometry constants affect only the threshold. The actual positively
oriented integer box satisfies precisely the source side exponents. -/
theorem markedMinorShear_good_integer_box_eventually {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ Y : ℝ in Filter.atTop, ∀ α : ℝ, MarkedMinorShearGood α Y →
      ∃ h l a b L T : ℤ, ∃ M N : ℕ, h*b-l*a=1 ∧
        Y^(1/10 : ℝ) ≤ (M : ℝ) ∧ Y^(1/10 : ℝ) ≤ (N : ℝ) ∧
        (M : ℝ)*(N : ℝ) ≤ 300*C^2*Y ∧
        (M : ℝ) ≤ Y^(9/10 : ℝ) ∧ (N : ℝ) ≤ Y^(9/10 : ℝ) ∧
        ∀ p : ℤ × ℤ, |(p.1 : ℝ)+(p.2 : ℝ)*α| ≤ C → |(p.2 : ℝ)/Y| ≤ C →
          markedMinorBasisCoords h l a b p ∈ markedMinorBox L T M N := by
  have h₁ := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).eventually_ge_atTop (30*C)
  have h₂ := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/5)).eventually_ge_atTop (20*C)
  filter_upwards [h₁,h₂,Filter.eventually_ge_atTop (1:ℝ)] with Y h₁ h₂ hY
  intro α hg
  have hYp : 0 < Y := by linarith
  obtain ⟨h,l,a,b,L,T,M,N,hd,hMlo,hNlo,hMN,hM,hN,hpoints⟩ :=
    markedMinorShear_good_integer_box α hY hC hg
  refine ⟨h,l,a,b,L,T,M,N,hd,hMlo,hNlo,hMN,?_,?_,hpoints⟩
  · calc
      (M : ℝ) ≤ (30*C)*Y^(4/5 : ℝ) := hM
      _ ≤ Y^(1/10 : ℝ)*Y^(4/5 : ℝ) := mul_le_mul_of_nonneg_right h₁ (by positivity)
      _ = Y^(9/10 : ℝ) := by rw [← Real.rpow_add hYp]; congr 1; norm_num
  · calc
      (N : ℝ) ≤ (20*C)*Y^(1/2 : ℝ) := hN
      _ ≤ Y^(2/5 : ℝ)*Y^(1/2 : ℝ) := mul_le_mul_of_nonneg_right h₂ (by positivity)
      _ = Y^(9/10 : ℝ) := by rw [← Real.rpow_add hYp]; congr 1; norm_num

end ArtinMatthews
