module

public import ArtinMatthews.MarkedActualVarianceProgressions
public import ArtinMatthews.MarkedVarianceModelBounds
public import ArtinMatthews.MarkedSieveAsymptotic
public import ArtinMatthews.MarkedSieveSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Prime variance bound for the actual marking arrays. Both the arithmetic
progression estimate and the independent-model variance bound have been
proved; the small-prime cutoff disappears by the test's support. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Topology

theorem marked_actual_prime_variance_upper {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (γ c : ℝ) (m : ℕ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
        Φ ((u : ℝ) / x) * markedArrayVarianceWeight
          (fun j i => markedLogPowerBand (e j i) x)
          (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u) ≤
        (((∫ t in Set.Ioc 0 T, Φ t) *
            (markedArrayVarianceConstant (Fintype.card I) / Fintype.card J) *
            Real.exp (-Real.eulerMascheroniConstant) / γ * (1 + Real.exp (-(m : ℝ) / 2)) + ε) *
          x / Real.log x) := by
  let H (x : ℝ) := markedArrayVarianceWeight (fun j i => markedLogPowerBand (e j i) x)
    (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x))
  let M (x : ℝ) := independentArraysVariance (fun j i => markedLogPowerBand (e j i) x)
    (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x))
  have hH : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ H x u :=
    Filter.Eventually.of_forall (fun _ _ => markedArrayVarianceWeight_nonneg _ _ _)
  have hM : ∀ᶠ x : ℝ in atTop, 0 ≤ M x ∧
      M x ≤ markedArrayVarianceConstant (Fintype.card I) / Fintype.card J :=
    marked_actual_variance_model_bounds e (fun j i => lt_trans (by norm_num) (he j i).1) hinj hJ
  have hprog := marked_actual_variance_progressions e he hinj hJ c 1 hc0 hc1
    Φ hT hΦ hderiv hΦT hΦ0
  have h := marked_sieve_asymptotic H M Φ T γ c
    (markedArrayVarianceConstant (Fintype.card I) / Fintype.card J) m
    hΦ0 hH hM hγ hm hlevel hprog hε
  filter_upwards [h, marked_prime_cutoff_eq_eventually (fun x => Finset.Icc 0 ⌊T * x⌋₊)
    H Φ ha hγ1 hlow] with x hx heq
  rw [heq] at hx
  exact hx

/-- The same arithmetic sieve gives an upper bound for the unmarked
smooth prime mass, required by the Cauchy step. -/
theorem marked_prime_test_mass_upper (γ c : ℝ) (m : ℕ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime), Φ ((u : ℝ) / x)) ≤
        (((∫ t in Set.Ioc 0 T, Φ t) * Real.exp (-Real.eulerMascheroniConstant) / γ *
            (1 + Real.exp (-(m : ℝ) / 2)) + ε) * x / Real.log x) := by
  have hprog := markedProgressionDiscrepancy_one_all_log c 1 hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
  have h := marked_sieve_asymptotic (fun _ _ => 1) (fun _ => 1) Φ T γ c 1 m hΦ0
    (Filter.Eventually.of_forall (fun _ _ => by norm_num))
    (Filter.Eventually.of_forall (fun _ => by norm_num)) hγ hm hlevel hprog hε
  filter_upwards [h, marked_prime_cutoff_eq_eventually (fun x => Finset.Icc 0 ⌊T * x⌋₊)
    (fun _ _ => 1) Φ ha hγ1 hlow] with x hx heq
  rw [heq] at hx
  simpa only [mul_one] using hx

end ArtinMatthews
