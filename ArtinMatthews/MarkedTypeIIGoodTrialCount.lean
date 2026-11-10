module

public import ArtinMatthews.MarkedTypeIIGoodFirst
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import Mathlib.CategoryTheory.Category.Basic
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
# Actual trial counts in the second good-state test

The trial values `DZ` use one omission tuple and one prime from each selected
band below the largest exponent. Their number is at most the size of that
explicit finite parameter space. For fixed smaller exponents its logarithm
is negligible compared with the largest logarithmic power. No prime-number
estimate is needed for this upper bound.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace ArtinMatthews

theorem markedBand_card_le_exp (a x : ℝ) :
    ((markedLogPowerBand a x).card : ℝ) ≤ Real.exp (2 * (Real.log x) ^ a) := by
  classical
  let N := ⌊Real.exp (2 * (Real.log x) ^ a)⌋₊
  have hsub : markedLogPowerBand a x ⊆ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpp, _hpl, hpu⟩ := mem_markedLogPowerBand.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.pos, (Nat.le_floor_iff (Real.exp_nonneg _)).mpr hpu⟩
  have hc : (markedLogPowerBand a x).card ≤ N := by
    simpa using Finset.card_le_card hsub
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.exp_nonneg _))

abbrev MarkedTrialPrimeChoices {ι : Type*} (b : ι → ℝ) (x : ℝ) :=
  ∀ i, ↥(markedLogPowerBand (b i) x)

/-- The actual finite set of trial products from omission choices and lower bands. -/
def markedGoodTrialValues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) (x : ℝ)
    (D : (Fin K → Fin (markedPadSlots x)) → ℕ) : Finset ℕ :=
  Finset.univ.image (fun z : (Fin K → Fin (markedPadSlots x)) × MarkedTrialPrimeChoices b x =>
    D z.1 * ∏ i, (z.2 i).val)

/-- Counting the explicit parameter space bounds the number of numeric trials. -/
theorem markedGoodTrialValues_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) (x : ℝ)
    (D : (Fin K → Fin (markedPadSlots x)) → ℕ) :
    (markedGoodTrialValues K b x D).card ≤
      (markedPadSlots x) ^ K * ∏ i, (markedLogPowerBand (b i) x).card := by
  simpa [markedGoodTrialValues, MarkedTrialPrimeChoices, Fintype.card_pi] using
    (Finset.card_image_le (s := Finset.univ)
      (f := fun z : (Fin K → Fin (markedPadSlots x)) × MarkedTrialPrimeChoices b x =>
        D z.1 * ∏ i, (z.2 i).val))

theorem markedGoodTrialValues_card_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) {x : ℝ} (hx : 1 ≤ Real.log x)
    (D : (Fin K → Fin (markedPadSlots x)) → ℕ) :
    ((markedGoodTrialValues K b x D).card : ℝ) ≤
      (2 : ℝ) ^ K * (Real.log x) ^ ((K : ℝ) / 100) *
        ∏ i, Real.exp (2 * (Real.log x) ^ b i) := by
  have hc := Nat.cast_le (α := ℝ).mpr (markedGoodTrialValues_card_le K b x D)
  push_cast at hc
  apply hc.trans
  apply mul_le_mul
  · exact markedPadSlots_pow_le K hx
  · exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => markedBand_card_le_exp (b i) x)
  · exact Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  · positivity

/-- Explicit logarithm of the upper envelope for the trial count. -/
def markedTrialLogEnvelope {ι : Type*} [Fintype ι] (K : ℕ) (b : ι → ℝ) (L : ℝ) : ℝ :=
  (K : ℝ) * Real.log 2 + ((K : ℝ) / 100) * Real.log L + 2 * ∑ i, L ^ b i

theorem markedTrialLogEnvelope_exp {ι : Type*} [Fintype ι]
    (K : ℕ) (b : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    Real.exp (markedTrialLogEnvelope K b L) =
      (2 : ℝ) ^ K * L ^ ((K : ℝ) / 100) * ∏ i, Real.exp (2 * L ^ b i) := by
  unfold markedTrialLogEnvelope
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hmid : Real.exp (((K : ℝ) / 100) * Real.log L) = L ^ ((K : ℝ) / 100) := by
    rw [Real.rpow_def_of_pos hL]
    congr 1
    ring
  rw [hmid, Finset.mul_sum, Real.exp_sum]

/-- The trial logarithm divided by the largest logarithmic power tends to zero. -/
theorem markedTrialLogEnvelope_div_tendsto {ι : Type*} [Fintype ι]
    (K : ℕ) (b : ι → ℝ) {a : ℝ} (ha : 0 < a) (hb : ∀ i, b i < a) :
    Tendsto (fun L : ℝ => markedTrialLogEnvelope K b L / L ^ a) atTop (nhds 0) := by
  have hconst : Tendsto (fun L : ℝ => ((K : ℝ) * Real.log 2) / L ^ a) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha)
  have hlog := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.const_mul ((K : ℝ) / 100)
  have hp (i : ι) : Tendsto (fun L : ℝ => L ^ b i / L ^ a) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (sub_pos.mpr (hb i))
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [show -(a - b i) = b i - a by ring, Real.rpow_sub hL]
  have hsum := (tendsto_finsetSum (s := Finset.univ) (fun i _ => hp i)).const_mul 2
  have htotal := (hconst.add hlog).add hsum
  simpa [markedTrialLogEnvelope, add_div, Finset.sum_div, mul_div_assoc, mul_comm] using htotal

/-- The actual number of trial integers is subexponential in the largest
logarithmic power, uniformly in the numeric omission products. -/
theorem markedGoodTrialValues_card_subexponential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (b : ι → ℝ) {a ε : ℝ} (ha : 0 < a) (hb : ∀ i, b i < a) (hε : 0 < ε)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ((markedGoodTrialValues K b x (D x)).card : ℝ) ≤
        Real.exp (ε * (Real.log x) ^ a) := by
  have hsmall := (markedTrialLogEnvelope_div_tendsto K b ha hb).eventually
    (gt_mem_nhds hε)
  filter_upwards [Real.tendsto_log_atTop.eventually hsmall,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hs hx
  have hx0 : 0 < Real.log x := by linarith
  apply (markedGoodTrialValues_card_bound K b hx (D x)).trans
  rw [← markedTrialLogEnvelope_exp K b hx0]
  apply Real.exp_le_exp.mpr
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos hx0 a)).mp hs |>.le

end ArtinMatthews
