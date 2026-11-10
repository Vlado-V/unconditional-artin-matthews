module

public import ArtinMatthews.MarkedMinorArcBanError
public import ArtinMatthews.MarkedBonferroniTail
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

/-! The actual growing slot count and logarithmic arc cutoff make ban error superlogarithmic. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedBanEnvelope (C A₀ x : ℝ) : ℝ :=
  C*(markedPadSlots x:ℝ)*((Real.log x)^A₀)^3*Real.exp (-((Real.log x)^(1/10:ℝ)))

theorem markedBanEnvelope_log_saving {C : ℝ} (hC : 0 ≤ C) (A₀ B : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x)^B*markedBanEnvelope C A₀ x) atTop (nhds 0) := by
  have hd := ((rpow_mul_exp_neg_rpow_tendsto (B+1/100+3*A₀)
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1)).comp Real.tendsto_log_atTop).const_mul (2*C)
  simp only [Function.comp_def,neg_mul,one_mul,mul_zero] at hd
  apply squeeze_zero' ?_ ?_ hd
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx
    unfold markedBanEnvelope
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx
    have hL : 0 < Real.log x := by linarith
    have hM := markedPadSlots_pow_le 1 hx
    norm_num at hM
    calc
      _ ≤ (Real.log x)^B*(C*(2*(Real.log x)^(1/100:ℝ))*((Real.log x)^A₀)^3*
          Real.exp (-((Real.log x)^(1/10:ℝ)))) := by
        unfold markedBanEnvelope
        gcongr
      _ = _ := by
        rw [← Real.rpow_mul_natCast hL.le]
        norm_num only [Nat.cast_ofNat]
        rw [show A₀*(3:ℝ)=3*A₀ by ring,Real.rpow_add hL,Real.rpow_add hL]
        ring

theorem markedBan_actual_row_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (source : (x : ℝ) → (j : J) → Fin (markedPadSlots x) → ↥(markedLogPowerBand (e j) x))
    (q r : ℝ → ℝ) (z w : ℝ → ℤ × ℤ) (D b : ℝ → ℤ)
    (ψ : ℝ → ℂ) (Y : ℝ → ℝ) {A W A₀ : ℝ} (hA : 0 ≤ A) (hW : 0 ≤ W) (hA₀ : 0 ≤ A₀)
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ A)
    (V : (x : ℝ) → MarkedFreshPrimeTuple e x → Finset (ℤ × ℤ))
    (test : (x : ℝ) → MarkedFreshPrimeTuple e x → (ℤ × ℤ) → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 0 ≤ q x ∧ q x ≤ 1 ∧ markedMinorIntegerDet (z x) (w x)=1 ∧
      markedMinorIntegerTau (r x) (z x) ≠ 0 ∧ 1 ≤ Y x ∧
      (∀ t v, v ∈ V x t → D x ∣ markedMinorIntegerDet (z x) v ∧
        |markedMinorIntegerTau (r x) v/markedMinorIntegerTau (r x) (z x)| ≤ 16) ∧
      (∀ t v, v ∈ V x t → ‖test x t v‖ ≤ 1)) (B : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x)^B*
      markedBanRowError e (q x) x (source x) (z x) (D x) (b x) ψ ((Real.log x)^A₀) (Y x) (V x) (test x))
      atTop (nhds 0) := by
  have hC : 0 ≤ markedBanErrorConstant (Fintype.card J) A W := by
    unfold markedBanErrorConstant
    positivity
  apply squeeze_zero' ?_ ?_ (markedBanEnvelope_log_saving hC A₀ B)
  · filter_upwards [hdata,marked_actual_tilted_atom_comparison_eventually e he,
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hatom hlog
    apply mul_nonneg (Real.rpow_nonneg (by linarith) _)
    apply Finset.sum_nonneg
    intro t _
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun j _ => (hatom (q x) hx.1 hx.2.1 j (t j)).1)
    · exact Finset.sum_nonneg (fun v _ => norm_nonneg _)
  · filter_upwards [hdata,markedBan_actual_row_error_eventually e he hinj,
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hrow hlog
    have hQ : 1 ≤ (Real.log x)^A₀ := Real.one_le_rpow hlog hA₀
    have hh := hrow (markedPadSlots x) (source x) (q x) (r x) (z x) (w x) (D x) (b x)
      ψ ((Real.log x)^A₀) (Y x) A W (V x) (test x) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
      hQ hx.2.2.2.2.1 hA hW hψ hsupp hx.2.2.2.2.2.1 hx.2.2.2.2.2.2
    exact mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by linarith) _)

end ArtinMatthews
