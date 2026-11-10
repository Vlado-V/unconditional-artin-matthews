module

public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedRawRootArcGrowth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! One explicit subpower envelope simultaneously controls the actual
omission counts, trial counts, integer frequencies and threshold inverses. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

def markedRawRootArcEnvelope (K : ℕ) (H a x : ℝ) : ℝ :=
  Real.exp ((10*((K:ℝ)+1)+H)*(Real.log x)^a)

theorem markedRawRootArcEnvelope_one_le (K : ℕ) {H a x : ℝ}
    (hH : 0 ≤ H) (hlog : 1 ≤ Real.log x) : 1 ≤ markedRawRootArcEnvelope K H a x := by
  unfold markedRawRootArcEnvelope
  apply Real.one_le_exp
  positivity

theorem markedRawRootArc_envelope_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β H a x : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hba : β+(1/100:ℝ) ≤ a) (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) :
    ((markedPadSlots x:ℝ)^(Fintype.card J) ≤ markedRawRootArcEnvelope (Fintype.card J) H a x) ∧
    (markedSourceFullProduct (markedRawNumericActive source):ℝ) ≤ markedRawRootArcEnvelope (Fintype.card J) H a x ∧
    (∀ I : Finset J,
      ((markedRawDirtyFullTrials e x source I).card:ℝ) ≤ markedRawRootArcEnvelope (Fintype.card J) H a x ∧
      ∀ u ∈ markedRawDirtyFullTrials e x source I,|(u:ℝ)| ≤ markedRawRootArcEnvelope (Fintype.card J) H a x) ∧
    (∀ I : Finset J,∀ p : MarkedFreshPrimeTuple (fun j : I => e j.1) x,
      |(markedFreshIntegerProduct (fun j : I => e j.1) x p:ℝ)| ≤ markedRawRootArcEnvelope (Fintype.card J) H a x) ∧
    (∀ j,1/Real.exp (-((Real.log x)^(e j))/4) ≤ markedRawRootArcEnvelope (Fintype.card J) H a x) := by
  let K : ℝ := Fintype.card J
  let t : ℝ := (Real.log x)^a
  let b : ℝ := (Real.log x)^β
  let M : ℝ := markedPadSlots x
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have ht : 0 ≤ t := Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hb : 0 ≤ b := Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hβa : β ≤ a := by linarith
  have hδa : (1/100:ℝ) ≤ a := by linarith
  have hbt : b ≤ t := Real.rpow_le_rpow_of_exponent_le hlog hβa
  have hM : M ≤ 2*(Real.log x)^(1/100:ℝ) := by
    simpa only [pow_one,Nat.cast_one] using markedPadSlots_pow_le 1 hlog
  have hMt : M ≤ 2*t := hM.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlog hδa) (by norm_num))
  have hMb : M*b ≤ 2*t := by
    calc
      _ ≤ 2*(Real.log x)^(1/100:ℝ)*b := mul_le_mul_of_nonneg_right hM hb
      _ = 2*(Real.log x)^((1/100:ℝ)+β) := by
        dsimp [b]
        rw [mul_assoc,← Real.rpow_add (zero_lt_one.trans_le hlog)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlog (by linarith)) (by norm_num)
  have hMexp : M ≤ Real.exp (2*t) := hMt.trans (by linarith [Real.add_one_le_exp (2*t)])
  have hp : M^(Fintype.card J) ≤ Real.exp (2*K*t) := by
    calc
      _ ≤ (Real.exp (2*t))^(Fintype.card J) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMexp _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have he6 : Real.exp (6*K*t) ≤ markedRawRootArcEnvelope (Fintype.card J) H a x := by
    apply Real.exp_le_exp.mpr
    change 6*K*t ≤ (10*(K+1)+H)*t
    nlinarith
  have he4 : Real.exp (4*K*t) ≤ Real.exp (6*K*t) := Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (2*K*t) ≤ Real.exp (4*K*t) := Real.exp_le_exp.mpr (by nlinarith)
  refine ⟨hp.trans (he2.trans (he4.trans he6)),?_,?_,?_,?_⟩
  · apply (markedRootArc_full_product_le e hlog he source).trans
    apply le_trans _ (he4.trans he6)
    apply Real.exp_le_exp.mpr
    change 2*K*M*b ≤ 4*K*t
    nlinarith
  · intro I
    constructor
    · apply (markedRootArc_trial_card_le e hlog he source I).trans
      calc
        _ ≤ Real.exp (2*K*t)*Real.exp (2*K*b) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
        _ = Real.exp (2*K*t+2*K*b) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (4*K*t) := Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ _ := he4.trans he6
    · intro u hu
      apply (markedRootArc_trial_abs_le e hlog he source I hu).trans
      apply le_trans _ he6
      apply Real.exp_le_exp.mpr
      change 2*K*(M+1)*b ≤ 6*K*t
      nlinarith
  · intro I p
    have hcard : (Fintype.card I:ℝ) ≤ K := by
      change (Fintype.card I:ℝ) ≤ (Fintype.card J:ℝ)
      exact_mod_cast (show Fintype.card I ≤ Fintype.card J by simpa only [Fintype.card_coe] using I.card_le_univ)
    have hh := markedRootArc_tuple_product_le (fun j : I => e j.1) hlog (fun j => he j.1) p
    have he : Real.exp (2*(Fintype.card I:ℝ)*b) ≤ Real.exp (2*K*t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul hcard hbt hb hK]
    apply le_trans _ (he.trans (he2.trans (he4.trans he6)))
    change |((∏ j : I,(p j:ℕ):ℕ):ℝ)| ≤ _
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact hh
  · intro j
    have hj : (Real.log x)^(e j) ≤ t := (Real.rpow_le_rpow_of_exponent_le hlog (he j)).trans hbt
    rw [one_div,← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    change -(-((Real.log x)^(e j))/4) ≤ (10*(K+1)+H)*t
    nlinarith

theorem markedRawRootArcEnvelope_cutoff {K : ℕ} {H a x Y : ℝ}
    (hH : 0 ≤ H) (ha : (1/5:ℝ) ≤ a) (hlog : 1 ≤ Real.log x)
    (hY : 1 ≤ Y) (hYhi : Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ))) :
    (⌊Y^(1/5:ℝ)⌋₊:ℝ) ≤ markedRawRootArcEnvelope K H a x := by
  calc
    _ ≤ Y^(1/5:ℝ) := Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hY) _)
    _ ≤ Y := by simpa using Real.rpow_le_rpow_of_exponent_le hY (by norm_num : (1/5:ℝ)≤1)
    _ ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) := hYhi
    _ ≤ Real.exp (H*(Real.log x)^a) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog ha) hH)
    _ ≤ _ := by
      change Real.exp (H*(Real.log x)^a) ≤ Real.exp ((10*((K:ℝ)+1)+H)*(Real.log x)^a)
      apply Real.exp_le_exp.mpr
      have ht : 0 ≤ (Real.log x)^a := Real.rpow_nonneg (zero_le_one.trans hlog) _
      have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
      nlinarith

end
end ArtinMatthews
