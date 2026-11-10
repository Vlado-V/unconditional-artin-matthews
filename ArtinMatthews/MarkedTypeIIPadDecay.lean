module

public import ArtinMatthews.MarkedTypeIIPadCollisions
public import ArtinMatthews.MarkedTypeIIGoodFirst
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedTypeIICollisionDecay
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Logarithmic savings for actual harmonic pad collisions

The pads are drawn from the actual closed prime band, with harmonic atom
`1/(p V)`, and their number is the paper's `floor((log x)^(1/100)) + 1`.
The finite iid collision theorem, the proved prime-band mass asymptotic,
and the band's actual lower endpoint give every fixed logarithmic saving.
No collision probability estimate is assumed.
-/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

/-- Actual harmonic probability of a repeated pad or a hit of a forbidden label. -/
noncomputable def markedActualPadCollision (a : ℝ)
    (F : (x : ℝ) → Finset ↥(markedLogPowerBand a x)) (x : ℝ) : ℝ :=
  markedEventMass
    (finiteProductMass (fun _ : Fin (markedPadSlots x) =>
      markedHarmonicAtom (markedLogPowerBand a x)))
    (MarkedPadCollision (F x))

theorem markedActualPadCollision_nonneg (a : ℝ)
    (F : (x : ℝ) → Finset ↥(markedLogPowerBand a x)) {x : ℝ}
    (hV : 0 < bandReciprocalMass (markedLogPowerBand a x)) :
    0 ≤ markedActualPadCollision a F x := by
  apply markedEventMass_nonneg
  exact marked_iid_mass_nonneg _ (fun _ => markedHarmonicAtom_nonneg _ hV)

/-- A common explicit bound, independent of the band exponent and forbidden labels. -/
theorem markedActualPadCollision_le {a x : ℝ}
    (F : (x : ℝ) → Finset ↥(markedLogPowerBand a x))
    (ha : (1 / 10 : ℝ) ≤ a) (hx : 1 ≤ Real.log x)
    (hV : Real.log 2 / 2 ≤ bandReciprocalMass (markedLogPowerBand a x))
    (hF : (F x).card ≤ 2) :
    markedActualPadCollision a F x ≤
      (24 / Real.log 2) * (Real.log x) ^ (1 / 50 : ℝ) *
        Real.exp (-(Real.log x) ^ (1 / 10 : ℝ)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hVpos : 0 < bandReciprocalMass (markedLogPowerBand a x) := by linarith
  have hslots := markedPadSlots_pow_le 2 hx
  norm_num at hslots
  have hMnat : 1 ≤ markedPadSlots x := by unfold markedPadSlots; omega
  have hM : (1 : ℝ) ≤ markedPadSlots x := by exact_mod_cast hMnat
  have hF' : ((F x).card : ℝ) ≤ 2 := by exact_mod_cast hF
  have hcount : (markedPadSlots x : ℝ) ^ 2 +
        (markedPadSlots x : ℝ) * (F x).card ≤
        12 * (Real.log x) ^ (1 / 50 : ℝ) := by
    have hf := mul_le_mul_of_nonneg_left hF' (by positivity : (0 : ℝ) ≤ markedPadSlots x)
    nlinarith
  have hatom : 1 / (Real.exp ((Real.log x) ^ (1 / 10 : ℝ)) *
        bandReciprocalMass (markedLogPowerBand a x)) ≤
      (2 / Real.log 2) * Real.exp (-(Real.log x) ^ (1 / 10 : ℝ)) := by
    calc
      _ ≤ 1 / (Real.exp ((Real.log x) ^ (1 / 10 : ℝ)) * (Real.log 2 / 2)) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le)
      _ = _ := by rw [Real.exp_neg]; field_simp
  have hcollision := marked_harmonic_pad_collision_bound
    (markedLogPowerBand a x) hVpos (Real.exp_pos ((Real.log x) ^ (1 / 10 : ℝ)))
    (fun p hp => marked_band_common_lower ha hx hp) (markedPadSlots x) (F x)
  change markedActualPadCollision a F x ≤ _ at hcollision
  apply hcollision.trans
  calc
    _ ≤ (12 * (Real.log x) ^ (1 / 50 : ℝ)) *
        ((2 / Real.log 2) * Real.exp (-(Real.log x) ^ (1 / 10 : ℝ))) :=
      mul_le_mul hcount hatom (by positivity) (by positivity)
    _ = _ := by ring

/-- The actual band mass supplies the positive normalizer in the common
pointwise bound. Only its eventual threshold depends on the fixed exponent. -/
theorem markedActualPadCollision_le_eventually {a : ℝ}
    (ha : (1 / 10 : ℝ) ≤ a)
    (F : (x : ℝ) → Finset ↥(markedLogPowerBand a x))
    (hF : ∀ x, (F x).card ≤ 2) :
    ∀ᶠ x : ℝ in atTop, markedActualPadCollision a F x ≤
      (24 / Real.log 2) * (Real.log x) ^ (1 / 50 : ℝ) *
        Real.exp (-(Real.log x) ^ (1 / 10 : ℝ)) := by
  have ha0 : 0 < a := by linarith
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    marked_log_power_band_mass_eventually ha0] with x hx hV
  exact markedActualPadCollision_le F ha hx hV.1.le (hF x)

/-- Actual harmonic pad collisions save every fixed logarithmic power. -/
theorem markedActualPadCollision_log_saving {a : ℝ}
    (ha : (1 / 10 : ℝ) ≤ a)
    (F : (x : ℝ) → Finset ↥(markedLogPowerBand a x))
    (hF : ∀ x, (F x).card ≤ 2) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * markedActualPadCollision a F x)
      atTop (nhds 0) := by
  have hdecay := ((rpow_mul_exp_neg_rpow_tendsto (A + 1 / 50)
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1)).comp
      Real.tendsto_log_atTop).const_mul (24 / Real.log 2)
  simp only [Function.comp_def, neg_mul, one_mul, mul_zero] at hdecay
  have ha0 : 0 < a := by linarith
  apply squeeze_zero' _ _ hdecay
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      marked_log_power_band_mass_eventually ha0] with x hx hV
    have hvpos : 0 < bandReciprocalMass (markedLogPowerBand a x) := by
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hv : Real.log 2 / 2 < bandReciprocalMass (markedLogPowerBand a x) := hV.1
      linarith
    exact mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log x) A)
      (markedActualPadCollision_nonneg a F hvpos)
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      markedActualPadCollision_le_eventually ha F hF] with x hx hb
    have h := mul_le_mul_of_nonneg_left hb
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log x) A)
    convert h using 1
    rw [Real.rpow_add (by linarith : 0 < Real.log x)]
    ring

end ArtinMatthews
