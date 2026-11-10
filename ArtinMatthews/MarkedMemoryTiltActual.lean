module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedTypeIIGoodFirst
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedMemoryTiltBasic
public import ArtinMatthews.MarkedTypeIICollisionDecay
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

/-! Sharp tilted-band mass control for the literal growing PD parameters. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ArtinMatthews

def markedMemoryTiltError (x : ℝ) : ℝ :=
  2*((markedMemoryMomentLength x : ℝ)+1) / Real.exp ((Real.log x)^(1/10:ℝ))

theorem markedRawActualPrimeAtom_sum_eq {J : Type*} (e : J → ℝ) (q x : ℝ) (j : J) :
    (∑ p : ↥(markedRawActualPrimeBand e x j), markedRawActualPrimeAtom e q x j p) =
      ∑ p : ↥(markedLogPowerBand (e j) x),
        markedTiltedBandAtom (markedLogPowerBand (e j) x) q (markedMemoryMomentLength x) p := by
  exact Equiv.sum_comp (markedRawPrimeBandEquiv _ (fun _ hp => (mem_markedLogPowerBand.mp hp).1))
    (markedTiltedBandAtom (markedLogPowerBand (e j) x) q (markedMemoryMomentLength x))

theorem markedMemory_actual_tilt_mass_error {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ j,
      |(∑ p : ↥(markedRawActualPrimeBand e x j), markedRawActualPrimeAtom e q x j p)-1| ≤
        markedMemoryTiltError x := by
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [hV, markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hV hN hlog
  intro q hq₀ hq₁ j
  rw [markedRawActualPrimeAtom_sum_eq]
  apply markedTiltedBandMass_error _
    ((by positivity : 0 < Real.log 2 / 2).trans (hV j).1) hq₀ hq₁ (Real.exp_pos _)
  intro p hp
  have hlo := marked_band_common_lower (he j) hlog hp
  exact ⟨(mem_markedLogPowerBand.mp hp).1.pos, hlo, hN p hlo⟩

/-- A polynomial-times-exponential envelope that tends to zero even after
the actual growing slot count has been included. -/
def markedMemoryBoundaryEnvelope (K : ℕ) (x : ℝ) : ℝ :=
  16*(K : ℝ)*(Real.log x)^2 * Real.exp (-(Real.log x)^(1/10:ℝ))

theorem markedMemoryBoundaryEnvelope_tendsto (K : ℕ) :
    Tendsto (markedMemoryBoundaryEnvelope K) atTop (𝓝 0) := by
  have h := rpow_mul_exp_neg_rpow_tendsto (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1/10) (by norm_num : (0 : ℝ) < 1)
  have h' := (h.const_mul (16*(K : ℝ))).comp Real.tendsto_log_atTop
  convert h' using 1
  · ext x
    simp only [markedMemoryBoundaryEnvelope, Function.comp_def, one_mul, neg_mul, Real.rpow_two]
    ring
  · simp

theorem markedMemory_boundary_exponent_le (K : ℕ) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    (K : ℝ)*(markedPadSlots x : ℝ)*markedMemoryTiltError x ≤ markedMemoryBoundaryEnvelope K x := by
  have hL : 0 ≤ Real.log x := le_trans (by norm_num) hlog
  have hpM : (Real.log x)^(1/100:ℝ) ≤ Real.log x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1/100:ℝ) ≤ 1)
  have hpN : (Real.log x)^(1/2:ℝ) ≤ Real.log x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1/2:ℝ) ≤ 1)
  have hM : (markedPadSlots x : ℝ) ≤ 2*Real.log x := by
    have hf := Nat.floor_le (Real.rpow_nonneg hL (1/100:ℝ))
    unfold markedPadSlots
    push_cast
    linarith
  have hN : (markedMemoryMomentLength x : ℝ)+1 ≤ 4*Real.log x := by
    have hc := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hL (1/2:ℝ)) (by norm_num : (0:ℝ) ≤ 2))
    unfold markedMemoryMomentLength
    push_cast
    linarith
  have hMN : (markedPadSlots x : ℝ)*(2*((markedMemoryMomentLength x : ℝ)+1)) ≤
      16*(Real.log x)^2 := by
    have hh := mul_le_mul hM (mul_le_mul_of_nonneg_left hN (by norm_num : (0:ℝ) ≤ 2))
      (by positivity : 0 ≤ 2*((markedMemoryMomentLength x : ℝ)+1)) (by positivity : 0 ≤ 2*Real.log x)
    nlinarith
  calc
    _ = (K : ℝ)*((markedPadSlots x : ℝ)*(2*((markedMemoryMomentLength x : ℝ)+1)))*
        Real.exp (-(Real.log x)^(1/10:ℝ)) := by
      rw [markedMemoryTiltError, Real.exp_neg]
      ring
    _ ≤ (K : ℝ)*(16*(Real.log x)^2)*Real.exp (-(Real.log x)^(1/10:ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMN (Nat.cast_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by unfold markedMemoryBoundaryEnvelope; ring

end ArtinMatthews
