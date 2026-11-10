module

public import ArtinMatthews.MarkedPhysicalRootTargetWindow
public import ArtinMatthews.MarkedRootArcComplexity
public import ArtinMatthews.MarkedProgressionGrowth
public import ArtinMatthews.MarkedRawRootArcComplexity
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual integer target window and positive bad-arc interval cost fit
inside every positive power. The copied marking divisor is retained. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedPhysicalRootTargetWindow_card_subpower
    (a H η : ℝ) (ha₀ : 0 ≤ a) (ha : a < 1) (hH : 0 ≤ H) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : ℤ) (A Y : ℝ), 0 ≤ A → 0 ≤ Y →
      |(D : ℝ)| * A * Y ≤ Real.exp (H*(Real.log x)^a) →
      ((markedPhysicalRootTargetWindow D A Y).card : ℝ) ≤ x^η := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    marked_sublinear_log_exp_le_rpow_eventually a (105+2*H) η ha hη] with x hlog hx
  intro D A Y hA hY hB
  let t := (Real.log x)^a
  let R := Real.exp (H*t)
  have ht : 1 ≤ t := Real.one_le_rpow hlog ha₀
  have hR : 1 ≤ R := Real.one_le_exp (by dsimp [t]; positivity)
  have hconst : (105 : ℝ) ≤ Real.exp (105*t) := by
    apply le_trans (show (105 : ℝ) ≤ Real.exp 105 by linarith [Real.add_one_le_exp 105])
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ (33+2*|(D : ℝ)| *A*Y)*(1+2*|(D : ℝ)| *A*Y) :=
      markedPhysicalRootTargetWindow_card_le D hA hY
    _ ≤ (35*R)*(3*R) := by
      apply mul_le_mul
      · dsimp [R] at hB ⊢
        nlinarith
      · dsimp [R] at hB ⊢
        nlinarith
      · positivity
      · positivity
    _ = 105*Real.exp (2*H*t) := by
      dsimp [R]
      rw [show 2*H*t = H*t+H*t by ring, Real.exp_add]
      ring
    _ ≤ Real.exp (105*t)*Real.exp (2*H*t) :=
      mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le
    _ = Real.exp ((105+2*H)*(Real.log x)^a) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      ring
    _ ≤ _ := hx

theorem markedPhysicalRoot_actual_error_budget
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (β H A η : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j, e j ≤ β) (hβhi : β+(1/100 : ℝ) < 1)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
        (o : J → Fin (markedPadSlots x)) (d₀ Y Q : ℝ),
        1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        0 ≤ Q → Q ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
        ((markedPhysicalRootTargetWindow
            (markedSourceCopiedProduct (markedRawNumericActive source) o : ℤ) A Y).card : ℝ) *
          markedRawBadRootArcComplexity e x d₀ Y source * Q^3 ≤ x^η := by
  let a : ℝ := max (β+1/100) (1/5)
  let C : ℝ := 10*((Fintype.card J : ℝ)+1)+H
  have ha : a < 1 := max_lt hβhi (by norm_num)
  have ha₀ : 0 ≤ a := le_trans (by norm_num) (le_max_right _ _)
  have hCa : 0 ≤ C+A+H := by dsimp [C]; positivity
  have hthird : 0 < η/3 := by positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℝ),
    markedPhysicalRootTargetWindow_card_subpower a (C+A+H) (η/3) ha₀ ha hCa hthird,
    markedRawBadRootArcComplexity_subpower e he β H (η/3) hβ heβ hβhi hH hthird,
    marked_sublinear_log_exp_le_rpow_eventually (1/5) (3*H) (η/3) (by norm_num) hthird]
    with x hlog hx0 hwindow harc hQpower
  intro source o d₀ Y Q hY hYhi hQ hQhi
  have hb := markedRawRootArc_envelope_bounds (a := a) e hβ hH
    (le_max_left _ _) hlog heβ source
  have hD : (markedSourceCopiedProduct (markedRawNumericActive source) o : ℝ) ≤
      Real.exp (C*(Real.log x)^a) := by
    have hp : 0 < markedSourceFullProduct (markedRawNumericActive source) :=
      Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (source j k).1.2.pos))
    exact (Nat.cast_le.mpr (Nat.le_of_dvd hp
      (markedSourceCopied_dvd_full (markedRawNumericActive source) o))).trans hb.2.1
  have hYbig : Y ≤ Real.exp (H*(Real.log x)^a) := hYhi.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (le_max_right _ _)) hH))
  have hAbig : A ≤ Real.exp (A*(Real.log x)^a) := by
    apply le_trans (show A ≤ Real.exp A by linarith [Real.add_one_le_exp A])
    apply Real.exp_le_exp.mpr
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left (Real.one_le_rpow hlog ha₀) hA)
  have hB : |((markedSourceCopiedProduct (markedRawNumericActive source) o : ℤ) : ℝ)| *A*Y ≤
      Real.exp ((C+A+H)*(Real.log x)^a) := by
    rw [Int.cast_natCast, abs_of_nonneg
      (Nat.cast_nonneg (markedSourceCopiedProduct (markedRawNumericActive source) o))]
    calc
      _ ≤ (Real.exp (C*(Real.log x)^a)*Real.exp (A*(Real.log x)^a))*
          Real.exp (H*(Real.log x)^a) :=
        mul_le_mul (mul_le_mul hD hAbig hA (Real.exp_pos _).le) hYbig
          (zero_le_one.trans hY) (by positivity)
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; ring
  have hwin := hwindow (markedSourceCopiedProduct (markedRawNumericActive source) o) A Y
    hA (zero_le_one.trans hY) hB
  have hac := harc source d₀ Y hY hYhi
  have hq : Q^3 ≤ x^(η/3) := by
    calc
      _ ≤ (Real.exp (H*(Real.log x)^(1/5 : ℝ)))^3 := pow_le_pow_left₀ hQ hQhi 3
      _ = Real.exp ((3*H)*(Real.log x)^(1/5 : ℝ)) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := hQpower
  have hpow : 0 ≤ x^(η/3) := (Real.rpow_pos_of_pos hx0 _).le
  calc
    _ ≤ (((markedPhysicalRootTargetWindow
        (markedSourceCopiedProduct (markedRawNumericActive source) o : ℤ) A Y).card : ℝ)*
        x^(η/3))*Q^3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hac (Nat.cast_nonneg _)) (pow_nonneg hQ 3)
    _ ≤ (x^(η/3)*x^(η/3))*Q^3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwin hpow) (pow_nonneg hQ 3)
    _ ≤ (x^(η/3)*x^(η/3))*x^(η/3) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg hpow hpow)
    _ = _ := by rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring

end ArtinMatthews
