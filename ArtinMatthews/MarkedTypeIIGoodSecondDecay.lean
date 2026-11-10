module

public import ArtinMatthews.MarkedTypeIIGoodSecond
public import ArtinMatthews.MarkedTypeIIGoodTrialCount
public import ArtinMatthews.MarkedBonferroniTail
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
# Decay of the actual second good-state error

The integer trial set is the image of the actual omission choices and the
prime choices in the smaller bands. Its proved subexponential cardinality,
combined with the circle/Markov estimate, gives arbitrary logarithmic saving.
The fresh product distribution may be any finite probability law on nonzero
integers; its atom sizes do not enter this good-state estimate.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology

namespace ArtinMatthews

def markedSecondTrialValues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) (x : ℝ)
    (D : (Fin K → Fin (markedPadSlots x)) → ℕ) : Finset ℤ :=
  (markedGoodTrialValues K b x D).image Int.ofNat

theorem markedSecondTrialValues_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) (x : ℝ)
    (D : (Fin K → Fin (markedPadSlots x)) → ℕ) :
    (markedSecondTrialValues K b x D).card ≤ (markedGoodTrialValues K b x D).card :=
  Finset.card_image_le

def markedSecondGoodError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) (a : ℝ)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ)
    (Ω : ℝ → Type*) [∀ x, Fintype (Ω x)]
    (T : ∀ x, Ω x → ℤ) (w : ∀ x, Ω x → ℝ) (x : ℝ) : ℝ :=
  volume.real {r | Real.exp (-((Real.log x) ^ a) / 4) ≤
    markedPairFailureProbability (markedSecondTrialValues K b x (D x))
      (T x) (w x) (100 * Real.exp (-((Real.log x) ^ a))) r}

/-- The actual trial count reduces the second good-state error to a fixed
exponential envelope. No cardinality or probability estimate is assumed. -/
theorem markedSecondGoodError_exp_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) {a : ℝ} (ha : 0 < a) (hb : ∀ i, b i < a)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ)
    (Ω : ℝ → Type*) [∀ x, Fintype (Ω x)]
    (T : ∀ x, Ω x → ℤ) (hT : ∀ x i, T x i ≠ 0)
    (w : ∀ x, Ω x → ℝ) (hw : ∀ x i, 0 ≤ w x i) (hwsum : ∀ x, ∑ i, w x i = 1) :
    ∀ᶠ x : ℝ in atTop, markedSecondGoodError K b a D Ω T w x ≤
      200 * Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ a) := by
  filter_upwards [markedGoodTrialValues_card_subexponential K b ha hb
    (by norm_num : (0 : ℝ) < 1 / 8) D] with x hx
  have hQ : ((markedSecondTrialValues K b x (D x)).card : ℝ) ≤
      Real.exp ((1 / 8 : ℝ) * (Real.log x) ^ a) :=
    (Nat.cast_le.mpr (markedSecondTrialValues_card_le K b x (D x))).trans hx
  have h := markedSecondGood_parameter_bound
    (markedSecondTrialValues K b x (D x)) (T x) (hT x) (w x) (hw x) (hwsum x)
    ((Real.log x) ^ a)
  change markedSecondGoodError K b a D Ω T w x ≤ _ at h
  apply h.trans
  calc
    200 * ((markedSecondTrialValues K b x (D x)).card : ℝ) ^ 2 *
        Real.exp (-3 * (Real.log x) ^ a / 4) ≤
        200 * (Real.exp ((1 / 8 : ℝ) * (Real.log x) ^ a)) ^ 2 *
          Real.exp (-3 * (Real.log x) ^ a / 4) := by gcongr
    _ = 200 * Real.exp (-(1 / 2 : ℝ) * (Real.log x) ^ a) := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The second good-state error saves every fixed logarithmic power for the
actual smaller prime bands and every finite fresh-product probability law. -/
theorem markedSecondGoodError_log_saving {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) {a : ℝ} (ha : 0 < a) (hb : ∀ i, b i < a)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ)
    (Ω : ℝ → Type*) [∀ x, Fintype (Ω x)]
    (T : ∀ x, Ω x → ℤ) (hT : ∀ x i, T x i ≠ 0)
    (w : ∀ x, Ω x → ℝ) (hw : ∀ x i, 0 ≤ w x i) (hwsum : ∀ x, ∑ i, w x i = 1)
    (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A * markedSecondGoodError K b a D Ω T w x)
      atTop (nhds 0) := by
  have hdecay := ((rpow_mul_exp_neg_rpow_tendsto A ha
    (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop).const_mul 200
  simp only [Function.comp_def, mul_zero] at hdecay
  apply squeeze_zero' _ _ hdecay
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) A) ENNReal.toReal_nonneg
  · filter_upwards [markedSecondGoodError_exp_bound K b ha hb D Ω T hT w hw hwsum,
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have h := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (Real.log_nonneg hx1) A)
    convert h using 1
    ring

end ArtinMatthews
