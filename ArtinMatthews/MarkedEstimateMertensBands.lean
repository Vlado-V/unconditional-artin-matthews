module

public import ArtinMatthews.MarkedEstimateMertensBandCore
public import PrimeNumberTheoremAnd.IEANTN.Mertens
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual reciprocal mass of the marking bands

The prime reciprocal sum theorem from the pinned PrimeNumberTheoremAnd
library proves the band's mass tends to `log 2`. Both endpoints match the
closed interval in the Artin–Matthews paper, including the possible prime
at the lower endpoint. No prime distribution hypothesis is assumed here.
-/

namespace ArtinMatthews

open scoped BigOperators

theorem markedPrimePrefix_eq_mertens (y : ℝ) :
    markedPrimePrefix y = Real.log (Real.log y) + Mertens.M + Mertens.E₂p y := by
  classical
  have hset : Nat.primesLE ⌊y⌋₊ = (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hle, hp⟩
      exact ⟨⟨hp.pos, hle⟩, hp⟩
    · rintro ⟨⟨_, hle⟩, hp⟩
      exact ⟨hle, hp⟩
  simpa only [markedPrimePrefix, hset] using Mertens.sum_prime_div_eq y

/-- Mertens' theorem for exactly the closed exponential marking band. -/
theorem marked_exponential_band_mass_tendsto :
    Filter.Tendsto
      (fun T : ℝ => markedClosedBandMass (Real.exp T) (Real.exp (2 * T)))
      Filter.atTop (nhds (Real.log 2)) :=
  marked_exponential_band_mass_tendsto_of_prefix Mertens.M Mertens.E₂p
    ((Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound')
    markedPrimePrefix_eq_mertens

/-- The reciprocal mass `V_i` in Section 2 tends to `log 2` for every fixed
positive band exponent. Its prescribed range `(0.1,0.2)` is more restrictive. -/
theorem marked_log_power_band_mass_tendsto {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun x : ℝ => ∑ p ∈ markedLogPowerBand a x, (1 : ℝ) / p)
      Filter.atTop (nhds (Real.log 2)) := by
  have hscale := (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  convert marked_exponential_band_mass_tendsto.comp hscale using 1
  funext x
  rfl

/-- Fixed bands eventually have mass bounded away from zero and below one. -/
theorem marked_log_power_band_mass_eventually {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log 2 / 2 < (∑ p ∈ markedLogPowerBand a x, (1 : ℝ) / p) ∧
        (∑ p ∈ markedLogPowerBand a x, (1 : ℝ) / p) < 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  exact (marked_log_power_band_mass_tendsto ha).eventually
    (Ioo_mem_nhds (by linarith) hupper)

end ArtinMatthews
