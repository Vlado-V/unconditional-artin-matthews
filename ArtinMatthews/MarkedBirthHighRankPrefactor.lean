module

public import ArtinMatthews.MarkedMinorArcProductMassActual
public import ArtinMatthews.MarkedTypeIIGoodFirst
public import ArtinMatthews.MarkedBirthRankCutoff
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

/-! The genuine initial active-tuple cost and the constant ghost rows fit
inside a fixed polynomial per operation at the actual M and N. -/

noncomputable section
namespace ArtinMatthews
open Filter

theorem markedBirth_initial_slots_le_twice_moment {x : ℝ} (hlog : 1 ≤ Real.log x) :
    markedPadSlots x ≤ 2*markedMemoryMomentLength x := by
  have hL : 0 ≤ Real.log x := zero_le_one.trans hlog
  have hM := Nat.floor_le (Real.rpow_nonneg hL (1/100:ℝ))
  have hpow : (Real.log x)^(1/100:ℝ) ≤ (Real.log x)^(1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hOne : 1 ≤ (Real.log x)^(1/2:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hN := markedMemoryMomentLength_lower hL
  have hh : (markedPadSlots x:ℝ) ≤ 2*(markedMemoryMomentLength x:ℝ) := by
    unfold markedPadSlots
    push_cast
    linarith
  exact_mod_cast hh

theorem markedBirth_high_rank_prefactor_budget (K : ℕ) (C P : ℝ)
    (hC : 1 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ x : ℝ in atTop, ∀ R : ℝ, 0 ≤ R → R ≤ (Real.log x)^P →
      (2:ℝ)^(K*markedPadSlots x)*C^(markedMemoryMomentLength x+1)*R^(markedMemoryMomentLength x) ≤
        ((Real.log x)^(P+2))^(markedMemoryMomentLength x+1) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max C ((2:ℝ)^(2*K))))] with x hx
  intro R hR hRp
  let L := Real.log x
  let N := markedMemoryMomentLength x
  have hLC : C ≤ L := (le_max_left _ _).trans hx
  have hLbase : (2:ℝ)^(2*K) ≤ L := (le_max_right _ _).trans hx
  have hL₁ : 1 ≤ L := hC.trans hLC
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hinit : (2:ℝ)^(K*markedPadSlots x) ≤ L^(N+1) := by
    calc
      _ ≤ (2:ℝ)^(K*(2*N)) := pow_le_pow_right₀ (by norm_num)
        (Nat.mul_le_mul_left K (markedBirth_initial_slots_le_twice_moment hL₁))
      _ = ((2:ℝ)^(2*K))^N := by rw [← pow_mul]; congr 1; ring
      _ ≤ L^N := pow_le_pow_left₀ (by positivity) hLbase N
      _ ≤ L^(N+1) := pow_le_pow_right₀ hL₁ (by omega)
  have hghost : C^(N+1) ≤ L^(N+1) := pow_le_pow_left₀ (zero_le_one.trans hC) hLC _
  have hedge : R^N ≤ (L^P)^(N+1) :=
    (pow_le_pow_left₀ hR hRp N).trans (pow_le_pow_right₀ (Real.one_le_rpow hL₁ hP) (by omega))
  calc
    _ ≤ L^(N+1)*L^(N+1)*(L^P)^(N+1) := by
      exact mul_le_mul (mul_le_mul hinit hghost (pow_nonneg (zero_le_one.trans hC) _) (by positivity))
        hedge (pow_nonneg hR _) (by positivity)
    _ = (L*L*L^P)^(N+1) := by rw [mul_pow,mul_pow]
    _ = _ := by
      congr 1
      calc
        L*L*L^P = (L^(1:ℝ)*L^(1:ℝ))*L^P := by rw [Real.rpow_one]
        _ = L^((1:ℝ)+1+P) := by rw [← Real.rpow_add hL,← Real.rpow_add hL]
        _ = _ := by congr 1; ring

end ArtinMatthews
