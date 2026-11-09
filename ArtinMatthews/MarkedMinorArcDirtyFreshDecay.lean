module

public import ArtinMatthews.MarkedMinorArcDirtyFreshGood


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform subset comparison and actual second-test root-exception bounds for the tilted law. -/
noncomputable section
namespace ArtinMatthews

open Filter Set MeasureTheory
open scoped BigOperators Topology

theorem marked_actual_fresh_subset_event_comparison_full_eventually {J : Type*}
    [Fintype J] [DecidableEq J] (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (I : Finset J) (q : ℝ), 0 ≤ q → q ≤ 1 →
      ∀ E : ((j : ↥I) → ↥(markedLogPowerBand (e j.1) x)) → Prop,
        markedEventMass (finiteProductMass (fun j : ↥I =>
          markedTiltedBandAtom (markedLogPowerBand (e j.1) x) q (markedMemoryMomentLength x))) E ≤
        (2:ℝ)^(Fintype.card J)*markedEventMass (finiteProductMass (fun j : ↥I =>
          markedHarmonicAtom (markedLogPowerBand (e j.1) x))) E := by
  filter_upwards [marked_actual_fresh_subset_event_comparison_eventually e he,
    marked_actual_tilted_atom_comparison_eventually e he] with x hx ha
  intro I q hq0 hq1 E
  have hm : 0 ≤ markedEventMass (finiteProductMass (fun j : ↥I =>
      markedHarmonicAtom (markedLogPowerBand (e j.1) x))) E := by
    apply markedEventMass_nonneg
    intro t
    apply Finset.prod_nonneg
    intro j _
    have hp := ha q hq0 hq1 j.1 (t j)
    linarith [hp.1,hp.2]
  have hc : (2:ℝ)^I.card ≤ (2:ℝ)^(Fintype.card J) :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ I)
  exact (hx I q hq0 hq1 E).trans (mul_le_mul_of_nonneg_right hc hm)

def markedTiltedSecondGoodError {A J : Type*} [Fintype A] [DecidableEq A]
    [Fintype J] [DecidableEq J] (K : ℕ) (b : A → ℝ) (a : ℝ)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ)
    (e : J → ℝ) (q x : ℝ) : ℝ :=
  volume.real {r : AddCircle (1:ℝ) | (2:ℝ)^(Fintype.card J)*Real.exp (-((Real.log x)^a)/4) ≤
    markedPairFailureProbability (markedSecondTrialValues K b x (D x))
      (markedFreshIntegerProduct e x) (markedFreshTiltedLaw e q x)
      (100*Real.exp (-((Real.log x)^a))) r}

/-- Existing Haar/Markov pair separation is instantiated with the actual
normalized harmonic prime-tuple law. The actual tilted law changes the
fresh-exception threshold by only 2^K, with no measure-growth premise. -/
theorem markedTiltedSecondGoodError_exp_bound {A J : Type*} [Fintype A] [DecidableEq A]
    [Fintype J] [DecidableEq J] (K : ℕ) (b : A → ℝ) {a : ℝ} (ha : 0 < a)
    (hb : ∀ i, b i < a) (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ)
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      markedTiltedSecondGoodError K b a D e q x ≤
        200*Real.exp (-(1/2:ℝ)*(Real.log x)^a) := by
  filter_upwards [marked_actual_fresh_failure_comparison_eventually e he,
    marked_actual_harmonic_fresh_probability_eventually e (fun j => by linarith [he j]),
    markedGoodTrialValues_card_subexponential K b ha hb (by norm_num : (0:ℝ)<1/8) D]
      with x hx hμ htrial
  intro q hq0 hq1
  have hsub : {r : AddCircle (1:ℝ) | (2:ℝ)^(Fintype.card J)*Real.exp (-((Real.log x)^a)/4) ≤
      markedPairFailureProbability (markedSecondTrialValues K b x (D x))
        (markedFreshIntegerProduct e x) (markedFreshTiltedLaw e q x)
        (100*Real.exp (-((Real.log x)^a))) r} ⊆
      {r | Real.exp (-((Real.log x)^a)/4) ≤
        markedPairFailureProbability (markedSecondTrialValues K b x (D x))
          (markedFreshIntegerProduct e x) (markedFreshHarmonicLaw e x)
          (100*Real.exp (-((Real.log x)^a))) r} := by
    intro r hr
    exact le_of_mul_le_mul_left (hr.trans (hx q hq0 hq1 _ _ r))
      (by positivity : 0 < (2:ℝ)^(Fintype.card J))
  have hroot := (measureReal_mono hsub).trans (markedSecondGood_parameter_bound
    (markedSecondTrialValues K b x (D x)) (markedFreshIntegerProduct e x)
    (markedFreshIntegerProduct_ne_zero e x) (markedFreshHarmonicLaw e x) hμ.1 hμ.2 ((Real.log x)^a))
  have hQ : ((markedSecondTrialValues K b x (D x)).card:ℝ) ≤
      Real.exp ((1/8:ℝ)*(Real.log x)^a) :=
    (Nat.cast_le.mpr (markedSecondTrialValues_card_le K b x (D x))).trans htrial
  apply hroot.trans
  calc
    200*((markedSecondTrialValues K b x (D x)).card:ℝ)^2*Real.exp (-3*(Real.log x)^a/4) ≤
        200*(Real.exp ((1/8:ℝ)*(Real.log x)^a))^2*Real.exp (-3*(Real.log x)^a/4) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
      congr 2
      ring

end ArtinMatthews
