module

public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMinorArcDirtySecondTrials
public import ArtinMatthews.MarkedMinorDirtyMajorBudget
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

/-! The actual full beta-root exceptional set has arbitrarily small
logarithmic circle measure, uniformly over all source active lists. -/
namespace ArtinMatthews
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem markedRawDirtyFullTrials_card_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (I : Finset J) (jstar : J) (hmax : ∀ j ∈ I,e j ≤ e jstar)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,∀ source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x),
      ((markedRawDirtyFullTrials e x source (I.erase jstar)).card:ℝ) ≤
        Real.exp (ε*(Real.log x)^(e jstar)) := by
  let b : ↥(I.erase jstar) → ℝ := fun j => e j.1
  have ha : 0 < e jstar := by linarith [he jstar]
  have hb : ∀ j : ↥(I.erase jstar),b j<e jstar :=
    markedRawDirty_other_exponents_lt e hinj I jstar hmax
  have hs := (markedTrialLogEnvelope_div_tendsto (Fintype.card J) b ha hb).eventually (gt_mem_nhds hε)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro source
  rw [markedRawDirtyFullTrials_eq_second]
  apply (Nat.cast_le.mpr (markedSecondTrialValues_card_le _ _ _ _)).trans
  apply (markedGoodTrialValues_card_bound (Fintype.card J) b hlog _).trans
  have hL : 0 < Real.log x := zero_lt_one.trans_le hlog
  rw [← markedTrialLogEnvelope_exp (Fintype.card J) b hL]
  exact Real.exp_le_exp.mpr ((div_lt_iff₀ (Real.rpow_pos_of_pos hL _)).mp hx).le

def markedRawDirtyBetaEvent {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x))
    (I : Finset J) (jstar : J) : Set (AddCircle (1:ℝ)) :=
  {a | Real.exp (-((Real.log x)^(e jstar))/4) ≤
    markedPairFailureProbability (markedRawDirtyFullTrials e x source (I.erase jstar))
      (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ I) => e j.1) x)
      (markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x)
      (100*Real.exp (-((Real.log x)^(e jstar)))) a}

theorem markedRawDirtyBetaEvent_measure_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (I : Finset J) (jstar : J) (hmax : ∀ j ∈ I,e j ≤ e jstar) :
    ∀ᶠ x : ℝ in atTop,∀ source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x),
      volume.real (markedRawDirtyBetaEvent e x source I jstar) ≤
        200*Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by
  let eF : ↥(Finset.univ \ I) → ℝ := fun j => e j.1
  filter_upwards [markedRawDirtyFullTrials_card_eventually e he hinj I jstar hmax
      (by norm_num : (0:ℝ)<1/8),
    marked_actual_harmonic_fresh_probability_eventually eF (fun j => by linarith [he j.1]),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hcard hμ hlog
  intro source
  have hr := markedSecondGood_parameter_bound (markedRawDirtyFullTrials e x source (I.erase jstar))
    (markedFreshIntegerProduct eF x) (markedFreshIntegerProduct_ne_zero eF x)
    (markedFreshHarmonicLaw eF x) hμ.1 hμ.2 ((Real.log x)^(e jstar))
  change volume.real (markedRawDirtyBetaEvent e x source I jstar) ≤ _ at hr
  apply hr.trans
  calc
    _ ≤ 200*(Real.exp ((1/8:ℝ)*(Real.log x)^(e jstar)))^2*
        Real.exp (-3*(Real.log x)^(e jstar)/4) := by gcongr; exact hcard source
    _ = 200*Real.exp (-(1/2:ℝ)*(Real.log x)^(e jstar)) := by
      rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by linarith [Real.rpow_le_rpow_of_exponent_le hlog (he jstar)])) (by norm_num)

def markedRawDirtyBetaBadRoots {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ)
    (source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x)) : Set (AddCircle (1:ℝ)) :=
  ⋃ p : Finset J × J,if p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2) then
    markedRawDirtyBetaEvent e x source p.1 p.2 else ∅

theorem markedRawDirtySecondGood_iff_not_bad {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r : ℝ) {B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z) :
    MarkedRawDirtySecondGood e x r w s ↔
      ((markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1:ℝ):AddCircle (1:ℝ)) ∉
        markedRawDirtyBetaBadRoots e x s.2.1 := by
  constructor
  · intro hg hb
    obtain ⟨⟨I,j⟩,h⟩ := Set.mem_iUnion.mp hb
    by_cases hp : j ∈ I ∧ (∀ i ∈ I,e i ≤ e j)
    · rw [ite_eq_left hp] at h
      exact hg I j hp.1 hp.2 h
    · rw [ite_eq_right hp] at h
      exact False.elim h
  · intro hg I j hj hm hb
    apply hg
    apply Set.mem_iUnion.mpr
    refine ⟨(I,j),?_⟩
    rw [ite_eq_left (show j ∈ I ∧ (∀ i ∈ I,e i ≤ e j) from ⟨hj,hm⟩)]
    exact hb

theorem markedRawDirtyBetaBadRoots_measure_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop,∀ source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x),
      volume.real (markedRawDirtyBetaBadRoots e x source) ≤
        (200*(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ))*
          Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by
  classical
  let GoodPair := {p : Finset J × J // p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)}
  have hall := eventually_all.mpr (fun p : GoodPair =>
    markedRawDirtyBetaEvent_measure_eventually e he hinj p.1.1 p.1.2 p.2.2)
  filter_upwards [hall] with x hx
  intro source
  unfold markedRawDirtyBetaBadRoots
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _p : Finset J × J,200*Real.exp (-(1/2:ℝ)*(Real.log x)^(1/10:ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p.2 ∈ p.1 ∧ (∀ j ∈ p.1,e j ≤ e p.2)
      · rw [ite_eq_left hp]
        exact hx (⟨p,hp⟩ : GoodPair) source
      · rw [ite_eq_right hp]
        simp only [measureReal_empty]
        positivity
    _ = _ := by simp [Fintype.card_prod,Fintype.card_finset]; ring

theorem markedRawDirtyBetaBadRoots_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (hinj : Function.Injective e) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,∀ source : MarkedRawActive (markedRawActualPrimeBand e x) (markedPadSlots x),
      volume.real (markedRawDirtyBetaBadRoots e x source) ≤ (Real.log x)^(-A) := by
  have h := marked_polynomial_exp_eventually_le
    (200*(2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ)) 0 A
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1)
  filter_upwards [markedRawDirtyBetaBadRoots_measure_eventually e he hinj,
    Real.tendsto_log_atTop.eventually h] with x hx hh
  intro source
  exact (hx source).trans (by simpa only [Real.rpow_zero,mul_one,one_mul] using hh)

end
end ArtinMatthews
