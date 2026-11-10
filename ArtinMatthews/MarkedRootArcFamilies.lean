module

public import ArtinMatthews.MarkedRootArcClipped
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Finite weighted elementary-arc families become exact interval sums.
The intervals are closed at both ends, including clips at zero and one. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRootArcFamily_indicator_sum {I E : Type*} [AddCommMonoid E]
    (S : Finset I) (q : I → ℤ) (ε : I → ℝ) (c : I → E)
    (hq : ∀ i ∈ S,q i ≠ 0) (hε : ∀ i ∈ S,ε i < (1/2:ℝ))
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (∑ i ∈ S,if (r:AddCircle (1:ℝ)) ∈ markedBadRootMultiple (q i) (ε i) then c i else 0) =
      ∑ i ∈ S,∑ k ∈ markedRootArcCenters (q i).natAbs,
        if r ∈ markedRootArcClippedInterval (q i).natAbs (ε i) k then c i else 0 := by
  apply Finset.sum_congr rfl
  intro i hi
  exact markedBadRootMultiple_clipped_indicator (q i) (hq i hi) (hε i hi) hr₀ hr₁ (c i)

theorem markedRootArcFamily_coefficient_mass {I : Type*}
    (S : Finset I) (q : I → ℤ) (c : I → ℂ) :
    (∑ i ∈ S,∑ _k ∈ markedRootArcCenters (q i).natAbs,‖c i‖) =
      ∑ i ∈ S,((q i).natAbs+1:ℕ)*‖c i‖ := by
  apply Finset.sum_congr rfl
  intro i _
  exact markedRootArcClipped_coefficient_mass (q i) (c i)

theorem markedRootArc_actual_widths_eventually
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop,
      (∀ j,0 ≤ 100*Real.exp (-((Real.log x)^(e j))) ∧
        100*Real.exp (-((Real.log x)^(e j))) < (1/2:ℝ)) ∧
      (∀ Y : ℝ,Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y →
        0 ≤ Y^(-7/10:ℝ) ∧ Y^(-7/10:ℝ) < (1/2:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => (Real.log x)^(1/10:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/10)).comp Real.tendsto_log_atTop
  have hb := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul 100
  simp only [mul_zero] at hb
  have hf := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (ht.const_mul_atTop (by norm_num : (0:ℝ)<7/10))
  filter_upwards [hb.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    hf.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hbx hfx hlog
  constructor
  · intro j
    refine ⟨by positivity,?_⟩
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hlog (he j)))) (by norm_num)).trans_lt hbx
  · intro Y hY
    have hY₀ : 0 < Y := (Real.exp_pos _).trans_le hY
    refine ⟨Real.rpow_nonneg hY₀.le _,?_⟩
    apply (Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hY (by norm_num : (-7/10:ℝ)≤0)).trans_lt
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    convert hfx using 1
    dsimp only [Function.comp_def]
    congr 1
    ring

end
end ArtinMatthews
