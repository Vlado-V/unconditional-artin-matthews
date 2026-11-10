module

public import ArtinMatthews.MarkedRootArcComplexity
public import ArtinMatthews.MarkedRawRootArcEnvelope
public import ArtinMatthews.MarkedProgressionGrowth
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual weighted interval-count cost is subpower. Fresh harmonic
weights and the inverse beta threshold remain in the exact cost. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawBadRootArcComplexity_le_envelope
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β H a x : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hba : β+(1/100:ℝ) ≤ a) (ha : (1/5:ℝ) ≤ a)
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    (hμ : ∀ I : Finset J,
      (∀ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ I) => e j.1) x,
        0 ≤ markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x t) ∧
      (∑ t,markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x t)=1)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (d₀ Y : ℝ) (hY : 1 ≤ Y) (hYhi : Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ))) :
    markedRawBadRootArcComplexity e x d₀ Y source ≤
      (2+3*((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ)))*
        (markedRawRootArcEnvelope (Fintype.card J) H a x)^5 := by
  let R := markedRawRootArcEnvelope (Fintype.card J) H a x
  have hR : 1 ≤ R := markedRawRootArcEnvelope_one_le (Fintype.card J) hH hlog
  have hR₀ : 0 ≤ R := zero_le_one.trans hR
  have hb := markedRawRootArc_envelope_bounds e hβ hH hba hlog he source
  have hcount : (Fintype.card (markedRawDyadicOmissions source d₀):ℝ) ≤ R := by
    have hh : Fintype.card (markedRawDyadicOmissions source d₀) ≤ (markedPadSlots x)^(Fintype.card J) := by
      simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using
        (Finset.card_le_univ (markedRawDyadicOmissions source d₀))
    exact (Nat.cast_le.mpr hh).trans (by simpa only [Nat.cast_pow] using hb.1)
  have hD (o : markedRawDyadicOmissions source d₀) :
      (markedSourceCopiedProduct (markedRawNumericActive source) o.1:ℝ) ≤ R := by
    have hp : 0 < markedSourceFullProduct (markedRawNumericActive source) :=
      Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (source j k).1.2.pos))
    exact (Nat.cast_le.mpr (Nat.le_of_dvd hp
      (markedSourceCopied_dvd_full (markedRawNumericActive source) o.1))).trans hb.2.1
  have hfirst : markedRawFirstRootArcComplexity source d₀ Y ≤ 2*R^4 :=
    markedFirstRootArcComplexity_le _ _ hR hcount
      (markedRawRootArcEnvelope_cutoff hH ha hlog hY hYhi) hD
  have hbeta : markedRawBetaRootArcComplexity e x source ≤
      ((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*(3*R^5) := by
    unfold markedRawBetaRootArcComplexity
    calc
      _ ≤ ∑ _p : Finset J × J,3*R^5 := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · have hpair (t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x) :
              markedPairRootArcComplexity (markedRawDirtyFullTrials e x source (p.1.erase p.2))
                (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t) ≤ 3*R^4 :=
            markedPairRootArcComplexity_le _ _ hR (hb.2.2.1 (p.1.erase p.2)).1
              (hb.2.2.1 (p.1.erase p.2)).2 (hb.2.2.2.1 (Finset.univ \ p.1) t)
          have hmean : (∑ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x,
              markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t*
                markedPairRootArcComplexity (markedRawDirtyFullTrials e x source (p.1.erase p.2))
                  (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ p.1) => e j.1) x t)) ≤ 3*R^4 := by
            calc
              _ ≤ ∑ t : MarkedFreshPrimeTuple (fun j : ↥(Finset.univ \ p.1) => e j.1) x,
                  markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ p.1) => e j.1) x t*(3*R^4) :=
                Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hpair t) ((hμ p.1).1 t))
              _ = _ := by rw [← Finset.sum_mul,(hμ p.1).2,one_mul]
          rw [div_eq_mul_inv]
          calc
            _ ≤ (3*R^4)*(Real.exp (-((Real.log x)^(e p.2))/4))⁻¹ :=
              mul_le_mul_of_nonneg_right hmean (inv_nonneg.mpr (Real.exp_pos _).le)
            _ ≤ (3*R^4)*R := mul_le_mul_of_nonneg_left
              (by simpa only [one_div] using hb.2.2.2.2 p.2) (by positivity)
            _ = _ := by ring
        · positivity
      _ = _ := by simp [Fintype.card_prod,Fintype.card_finset]
  have hp45 : R^4 ≤ R^5 := by simpa only [pow_succ,mul_one] using
    (mul_le_mul_of_nonneg_left hR (pow_nonneg hR₀ 4))
  unfold markedRawBadRootArcComplexity
  calc
    _ ≤ 2*R^4+((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*(3*R^5) := add_le_add hfirst hbeta
    _ ≤ 2*R^5+((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*(3*R^5) := by gcongr
    _ = _ := by ring

theorem markedRawBadRootArcComplexity_subpower
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (β H η : ℝ)
    (hβ : 0 ≤ β) (heβ : ∀ j,e j ≤ β) (hβhi : β+(1/100:ℝ)<1)
    (hH : 0 ≤ H) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,∀ (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
      (d₀ Y : ℝ),1 ≤ Y → Y ≤ Real.exp (H*(Real.log x)^(1/5:ℝ)) →
      markedRawBadRootArcComplexity e x d₀ Y source ≤ x^η := by
  let a : ℝ := max (β+1/100) (1/5)
  let C : ℝ := 2+3*((2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))
  let D : ℝ := 10*((Fintype.card J:ℝ)+1)+H
  have ha : a<1 := max_lt hβhi (by norm_num)
  have ha₀ : 0 ≤ a := le_trans (by norm_num) (le_max_right _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hμ := eventually_all.mpr (fun I : Finset J =>
    marked_actual_harmonic_fresh_probability_eventually (fun j : ↥(Finset.univ \ I) => e j.1)
      (fun j => by linarith [he j.1]))
  filter_upwards [hμ,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    marked_sublinear_log_exp_le_rpow_eventually a (C+5*D) η ha hη] with x hμx hlog hx
  intro source d₀ Y hY hYhi
  have hc : C ≤ Real.exp (C*(Real.log x)^a) := by
    apply le_trans (show C ≤ Real.exp C by linarith [Real.add_one_le_exp C])
    exact Real.exp_le_exp.mpr (by nlinarith [Real.one_le_rpow hlog ha₀])
  calc
    _ ≤ C*(markedRawRootArcEnvelope (Fintype.card J) H a x)^5 :=
      markedRawBadRootArcComplexity_le_envelope e hβ hH (le_max_left _ _) (le_max_right _ _)
        hlog heβ hμx source d₀ Y hY hYhi
    _ ≤ Real.exp (C*(Real.log x)^a)*(markedRawRootArcEnvelope (Fintype.card J) H a x)^5 :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp ((C+5*D)*(Real.log x)^a) := by
      unfold markedRawRootArcEnvelope
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      dsimp [D]
      ring
    _ ≤ _ := hx

end
end ArtinMatthews
