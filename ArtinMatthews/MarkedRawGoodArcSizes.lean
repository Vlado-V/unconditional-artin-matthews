module

public import ArtinMatthews.MarkedRawGoodArcFamily
public import ArtinMatthews.MarkedRawRootArcEnvelope
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

/-! Unweighted counts for the actual first/beta arc family. Every fresh
tuple is counted; weighted exceptional-mass bounds are not substituted. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedRawGood_fresh_card_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β H a x : ℝ} (_hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hba : β+(1/100:ℝ) ≤ a) (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β) (I : Finset J) :
    (Fintype.card (MarkedFreshPrimeTuple (fun j : I => e j.1) x):ℝ) ≤
      markedRawRootArcEnvelope (Fintype.card J) H a x := by
  have hb : (Real.log x)^β ≤ (Real.log x)^a :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  have hc : (Fintype.card I:ℝ) ≤ (Fintype.card J:ℝ) := by
    exact_mod_cast (show Fintype.card I ≤ Fintype.card J by simpa only [Fintype.card_coe] using I.card_le_univ)
  calc
    _ = ∏ j : I,((markedLogPowerBand (e j.1) x).card:ℝ) := by
      simp only [MarkedFreshPrimeTuple,Fintype.card_pi,Fintype.card_coe,Nat.cast_prod]
    _ ≤ ∏ _j : I,Real.exp (2*(Real.log x)^β) := by
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      intro j _
      exact (markedBand_card_le_exp (e j.1) x).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (he j.1)) (by norm_num)))
    _ = Real.exp (2*(Fintype.card I:ℝ)*(Real.log x)^β) := by
      simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ (Real.log x)^β := Real.rpow_nonneg (zero_le_one.trans hlog) _
      have h1 : 0 ≤ (Real.log x)^a := Real.rpow_nonneg (zero_le_one.trans hlog) _
      have hcard : 0 ≤ (Fintype.card J:ℝ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul hc hb h0 hcard]

theorem markedRawGoodArcIndex_card_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β H a x : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hba : β+(1/100:ℝ) ≤ a) (ha : (1/5:ℝ) ≤ a)
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (hY : 1 ≤ Y) (hYhi : Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ))) :
    (Fintype.card (MarkedRawGoodArcIndex e x source d₀ Y):ℝ) ≤
      (1+(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*(markedRawRootArcEnvelope (Fintype.card J) H a x)^3 := by
  let A := markedRawRootArcEnvelope (Fintype.card J) H a x
  have hA : 1 ≤ A := markedRawRootArcEnvelope_one_le _ hH hlog
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hb := markedRawRootArc_envelope_bounds e hβ hH hba hlog he source
  have hO : (Fintype.card (markedRawDyadicOmissions source d₀):ℝ) ≤ A := by
    have hh : Fintype.card (markedRawDyadicOmissions source d₀) ≤ (markedPadSlots x)^(Fintype.card J) := by
      simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using
        Finset.card_le_univ (markedRawDyadicOmissions source d₀)
    exact (Nat.cast_le.mpr hh).trans (by simpa only [Nat.cast_pow] using hb.1)
  have hL : (⌊Y^(1/5:ℝ)⌋₊:ℝ) ≤ A := markedRawRootArcEnvelope_cutoff hH ha hlog hY hYhi
  have hfirst : (Fintype.card (MarkedRawFirstArcIndex source d₀ Y):ℝ) ≤ A^2 := by
    calc
      _ = (Fintype.card (markedRawDyadicOmissions source d₀):ℝ)*(⌊Y^(1/5:ℝ)⌋₊:ℝ) := by
        simp [MarkedRawFirstArcIndex,Fintype.card_prod]
      _ ≤ A*A := mul_le_mul hO hL (Nat.cast_nonneg _) hA0
      _ = _ := by ring
  have hbeta : (Fintype.card (MarkedRawBetaArcIndex e x source):ℝ) ≤
      ((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*A^3 := by
    simp only [MarkedRawBetaArcIndex,Fintype.card_sigma,Nat.cast_sum,Fintype.card_prod,
      Fintype.card_coe,Nat.cast_mul]
    calc
      _ ≤ ∑ _p : Finset J × J,A^3 := by
        apply Finset.sum_le_sum
        intro p _
        have hf := markedRawGood_fresh_card_envelope e hβ hH hba hlog he (Finset.univ \ p.1)
        have hq := (hb.2.2.1 (p.1.erase p.2)).1
        calc
          _ ≤ A*(A*A) := mul_le_mul hf (mul_le_mul hq hq (Nat.cast_nonneg _) hA0)
            (by positivity) hA0
          _ = _ := by ring
      _ = _ := by simp [Fintype.card_prod,Fintype.card_finset]
  have hp23 : A^2 ≤ A^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg A)]
  calc
    _ = (Fintype.card (MarkedRawFirstArcIndex source d₀ Y):ℝ)+(Fintype.card (MarkedRawBetaArcIndex e x source):ℝ) := by
      simp only [MarkedRawGoodArcIndex,Fintype.card_sum,Nat.cast_add]
    _ ≤ A^2+((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*A^3 := add_le_add hfirst hbeta
    _ ≤ _ := by dsimp only [A]; nlinarith

theorem markedRawGoodArcFrequency_envelope {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β H a x : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hba : β+(1/100:ℝ) ≤ a) (ha : (1/5:ℝ) ≤ a)
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (hY : 1 ≤ Y) (hYhi : Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)))
    (i : MarkedRawGoodArcIndex e x source d₀ Y) :
    |(markedRawGoodArcFrequency e x source d₀ Y i:ℝ)| ≤
      2*(markedRawRootArcEnvelope (Fintype.card J) H a x)^2 := by
  let A := markedRawRootArcEnvelope (Fintype.card J) H a x
  have hA : 0 ≤ A := zero_le_one.trans (markedRawRootArcEnvelope_one_le _ hH hlog)
  have hb := markedRawRootArc_envelope_bounds e hβ hH hba hlog he source
  cases i with
  | inl p =>
      have hd : (markedSourceCopiedProduct (markedRawNumericActive source) p.1.1:ℝ) ≤ A := by
        have hp : 0 < markedSourceFullProduct (markedRawNumericActive source) :=
          Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (source j k).1.2.pos))
        exact (Nat.cast_le.mpr (Nat.le_of_dvd hp (markedSourceCopied_dvd_full _ p.1.1))).trans hb.2.1
      have hl : (p.2.1:ℝ) ≤ A := (Nat.cast_le.mpr (Finset.mem_Icc.mp p.2.2).2).trans
        (markedRawRootArcEnvelope_cutoff hH ha hlog hY hYhi)
      have hf : (markedRawGoodArcFrequency e x source d₀ Y (Sum.inl p):ℝ) =
          (markedSourceCopiedProduct (markedRawNumericActive source) p.1.1:ℝ)*(p.2.1:ℝ) := by
        simp [markedRawGoodArcFrequency]
      rw [hf,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      exact (mul_le_mul hd hl (Nat.cast_nonneg _) hA).trans (by nlinarith [sq_nonneg A])
  | inr p =>
      have hu := (hb.2.2.1 (p.1.1.erase p.1.2)).2 p.2.2.1.1 p.2.2.1.2
      have hv := (hb.2.2.1 (p.1.1.erase p.1.2)).2 p.2.2.2.1 p.2.2.2.2
      have ht := hb.2.2.2.1 (Finset.univ \ p.1.1) p.2.1
      have huv : |(p.2.2.1.1:ℝ)-(p.2.2.2.1:ℝ)| ≤ 2*A := by
        have hh := abs_sub_le (p.2.2.1.1:ℝ) 0 (p.2.2.2.1:ℝ)
        simp only [sub_zero,zero_sub,abs_neg] at hh
        linarith
      simp only [markedRawGoodArcFrequency,Int.cast_mul,Int.cast_sub,abs_mul]
      exact (mul_le_mul huv ht (abs_nonneg _) (by positivity)).trans_eq (by ring)

end ArtinMatthews
