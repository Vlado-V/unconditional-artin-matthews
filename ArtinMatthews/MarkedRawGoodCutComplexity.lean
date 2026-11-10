module

public import ArtinMatthews.MarkedRawGoodArcFamily
public import ArtinMatthews.MarkedRawRootArcEnvelope
public import ArtinMatthews.MarkedProgressionGrowth
public import ArtinMatthews.MarkedRawGoodArcSizes
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Unweighted endpoint complexity of the complete literal first/beta
cutoff, including all fresh tuples and the possible Möbius pole. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawGoodArcLevels_card_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β H a x : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hba : β+(1/100:ℝ) ≤ a) (ha : (1/5:ℝ) ≤ a)
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y R : ℝ) (hY : 1 ≤ Y) (hYhi : Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)))
    (hR : 0 ≤ R) (hRA : R ≤ markedRawRootArcEnvelope (Fintype.card J) H a x) :
    ((markedRawGoodArcLevels e x source d₀ Y R).card:ℝ) ≤
      18*(1+(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*
        (markedRawRootArcEnvelope (Fintype.card J) H a x)^6 := by
  let A := markedRawRootArcEnvelope (Fintype.card J) H a x
  have hA : 1 ≤ A := markedRawRootArcEnvelope_one_le _ hH hlog
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hc := markedRawGoodArcIndex_card_envelope e hβ hH hba ha hlog he source d₀ Y hY hYhi
  have hi (i : MarkedRawGoodArcIndex e x source d₀ Y) :
      ((markedRootLiftedArcLevels (markedRawGoodArcFrequency e x source d₀ Y i) R
        (markedRawGoodArcWidth e x source d₀ Y i)).card:ℝ) ≤ 18*A^3 := by
    have hf := markedRawGoodArcFrequency_envelope e hβ hH hba ha hlog he source d₀ Y hY hYhi i
    have hf' : ((markedRawGoodArcFrequency e x source d₀ Y i).natAbs:ℝ) ≤ 2*A^2 := by
      rw [Nat.cast_natAbs,Int.cast_abs]
      exact hf
    calc
      _ ≤ 4*((markedRawGoodArcFrequency e x source d₀ Y i).natAbs:ℝ)*R+10 :=
        markedRootLiftedArcLevels_card_le _ hR
      _ ≤ 4*(2*A^2)*A+10 := by gcongr
      _ ≤ _ := by nlinarith [show (1:ℝ) ≤ A^3 from one_le_pow₀ hA]
  have hb : ((markedRawGoodArcLevels e x source d₀ Y R).card:ℝ) ≤
      ∑ i : MarkedRawGoodArcIndex e x source d₀ Y,
        ((markedRootLiftedArcLevels (markedRawGoodArcFrequency e x source d₀ Y i) R
          (markedRawGoodArcWidth e x source d₀ Y i)).card:ℝ) := by
    exact_mod_cast (show (markedRawGoodArcLevels e x source d₀ Y R).card ≤
      ∑ i : MarkedRawGoodArcIndex e x source d₀ Y,
        (markedRootLiftedArcLevels (markedRawGoodArcFrequency e x source d₀ Y i) R
          (markedRawGoodArcWidth e x source d₀ Y i)).card from Finset.card_biUnion_le)
  calc
    _ ≤ _ := hb
    _ ≤ ∑ _i : MarkedRawGoodArcIndex e x source d₀ Y,18*A^3 := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card (MarkedRawGoodArcIndex e x source d₀ Y):ℝ)*(18*A^3) := by simp
    _ ≤ ((1+(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*A^3)*(18*A^3) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem markedRawGood_allCuts_card_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β H a x : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hba : β+(1/100:ℝ) ≤ a) (ha : (1/5:ℝ) ≤ a)
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y R : ℝ) (hY : 1 ≤ Y) (hYhi : Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)))
    (hR : 0 ≤ R) (hRA : R ≤ markedRawRootArcEnvelope (Fintype.card J) H a x)
    (z w : Fin 2 → ℝ) :
    ((markedTransportedRatioAllCuts z w (markedRawGoodArcLevels e x source d₀ Y R)).card:ℝ) ≤
      (18*(1+(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))+1)*
        (markedRawRootArcEnvelope (Fintype.card J) H a x)^6 := by
  have hc := markedRawGoodArcLevels_card_envelope e hβ hH hba ha hlog he source d₀ Y R hY hYhi hR hRA
  have hA : (1:ℝ) ≤ (markedRawRootArcEnvelope (Fintype.card J) H a x)^6 :=
    one_le_pow₀ (markedRawRootArcEnvelope_one_le (Fintype.card J) hH hlog)
  have hh : ((markedTransportedRatioAllCuts z w (markedRawGoodArcLevels e x source d₀ Y R)).card:ℝ) ≤
      ((markedRawGoodArcLevels e x source d₀ Y R).card:ℝ)+1 := by
    exact_mod_cast markedTransportedRatioAllCuts_card_le z w (markedRawGoodArcLevels e x source d₀ Y R)
  nlinarith

theorem markedRawGood_allCuts_subpower {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (β H η : ℝ) (hβ : 0 ≤ β) (he : ∀ j,e j ≤ β)
    (hβhi : β+(1/100:ℝ)<1) (hH : 0 ≤ H) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
      (d₀ Y R : ℝ) (z w : Fin 2 → ℝ),1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      0 ≤ R → R ≤ Real.exp (H*(Real.log x)^(max (β+1/100) (1/5))) →
      ((markedTransportedRatioAllCuts z w (markedRawGoodArcLevels e x source d₀ Y R)).card:ℝ) ≤ x^η := by
  let a : ℝ := max (β+1/100) (1/5)
  let C : ℝ := 18*(1+(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))+1
  let D : ℝ := 10*((Fintype.card J:ℝ)+1)+H
  have ha : a<1 := max_lt hβhi (by norm_num)
  have ha0 : 0 ≤ a := le_trans (by norm_num) (le_max_right _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    marked_sublinear_log_exp_le_rpow_eventually a (C+6*D) η ha hη] with x hlog hx
  intro source d₀ Y R z w hY hYhi hR hRhi
  have hRA : R ≤ markedRawRootArcEnvelope (Fintype.card J) H a x := by
    apply hRhi.trans
    apply Real.exp_le_exp.mpr
    change H*(Real.log x)^a ≤ (10*((Fintype.card J:ℝ)+1)+H)*(Real.log x)^a
    have ht : 0 ≤ (Real.log x)^a := Real.rpow_nonneg (zero_le_one.trans hlog) _
    have hk : 0 ≤ (Fintype.card J:ℝ) := Nat.cast_nonneg _
    nlinarith
  have hc : C ≤ Real.exp (C*(Real.log x)^a) := by
    apply le_trans (show C ≤ Real.exp C by linarith [Real.add_one_le_exp C])
    exact Real.exp_le_exp.mpr (by nlinarith [Real.one_le_rpow hlog ha0])
  calc
    _ ≤ C*(markedRawRootArcEnvelope (Fintype.card J) H a x)^6 :=
      markedRawGood_allCuts_card_envelope e hβ hH (le_max_left _ _) (le_max_right _ _)
        hlog he source d₀ Y R hY hYhi hR hRA z w
    _ ≤ Real.exp (C*(Real.log x)^a)*(markedRawRootArcEnvelope (Fintype.card J) H a x)^6 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp ((C+6*D)*(Real.log x)^a) := by
      unfold markedRawRootArcEnvelope
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      dsimp [D]
      ring
    _ ≤ _ := hx

end ArtinMatthews
