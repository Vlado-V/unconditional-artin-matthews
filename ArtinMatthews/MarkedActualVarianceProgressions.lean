module

public import ArtinMatthews.MarkedActualCrossProgressions
public import ArtinMatthews.MarkedVarianceFamily
public import ArtinMatthews.MarkedProgressionLinear


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nonnegative variance weight Z_b has the all-logarithmic
summed predecessor-progression estimate with its exact independent-model
mean. This is obtained from the proved constant, first, repeated, and cross
moment estimates; no progression remainder is assumed. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Asymptotics Topology

theorem marked_actual_variance_progressions {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (c A : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedProgressionDiscrepancy
      (markedArrayVarianceWeight (fun j i => markedLogPowerBand (e j i) x)
        (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)))
      (independentArraysVariance (fun j i => markedLogPowerBand (e j i) x)
        (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x))) Φ T x ⌊x ^ c⌋₊) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  classical
  let P (x : ℝ) (j : J) (i : I) := markedLogPowerBand (e j i) x
  let W (x : ℝ) (j : J) (i : I) := bandReciprocalMass (P x j i)
  let μ (x : ℝ) (j : J) := independentArrayMean (P x j) (W x j)
  let ν (x : ℝ) (j : J) := independentArraySecondMoment (P x j) (W x j)
  let w (x : ℝ) (j : J) (u : ℕ) := divisorWeight Finset.univ (P x j) (W x j) u
  let b (x : ℝ) := markedVarianceCoefficient (μ x)
  let H (x : ℝ) (q : MarkedVarianceIndex J) (u : ℕ) :=
    markedVarianceValue (fun j => w x j u) q
  let M (x : ℝ) := markedVarianceModel (μ x) (ν x)
  let v : ℝ := (1 / 2 : ℝ) ^ Fintype.card I
  have hv : 0 < v := by dsimp [v]; positivity
  have hrow (j : J) : Function.Injective (e j) := by
    intro i k hik
    have hp : (j, i) = (j, k) := hinj hik
    exact congrArg Prod.snd hp
  have hcross (j k : J) (hjk : j ≠ k) : Function.Injective (Sum.elim (e j) (e k)) := by
    intro p q hpq
    cases p with
    | inl i =>
      cases q with
      | inl l => exact congrArg Sum.inl (hrow j hpq)
      | inr l =>
        have hpair : (j, i) = (k, l) := hinj hpq
        exact (hjk (congrArg Prod.fst hpair)).elim
    | inr i =>
      cases q with
      | inl l =>
        have hpair : (k, i) = (j, l) := hinj hpq
        exact (hjk (congrArg Prod.fst hpair).symm).elim
      | inr l => exact congrArg Sum.inr (hrow k hpq)
  have hmean : ∀ᶠ x : ℝ in atTop, ∀ j, v ≤ μ x j := by
    apply eventually_all.mpr
    intro j
    filter_upwards [marked_array_moment_bounds_eventually (e j)
      (fun i => lt_trans (by norm_num) (he j i).1)] with x hx
    exact hx.1
  have hb : ∀ᶠ x : ℝ in atTop, ∀ q ∈ (Finset.univ : Finset (MarkedVarianceIndex J)),
      |b x q| ≤ 1 + 2 / v + 1 / v ^ 2 := by
    filter_upwards [hmean] with x hx
    exact fun q _ => markedVarianceCoefficient_bound (μ x) hv hx hJ q
  have herror (q : MarkedVarianceIndex J) :
      (fun x : ℝ => markedProgressionDiscrepancy (H x q) (M x q) Φ T x ⌊x ^ c⌋₊) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
    rcases q with q | j | ⟨j, k⟩
    · exact markedProgressionDiscrepancy_one_all_log c A hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
    · exact marked_actual_first_moment_progressions (e j) (he j) (hrow j) c A hc0 hc1
        Φ hT hΦ hderiv hΦT hΦ0
    · by_cases hjk : j = k
      · subst k
        have h := marked_actual_second_moment_progressions (e j) (he j) (hrow j) c A hc0 hc1
          Φ hT hΦ hderiv hΦT hΦ0
        simpa only [H, M, markedVarianceValue, markedVarianceModel, markedVariancePairModel,
          ite_true, w, μ, ν, P, W, pow_two] using h
      · have h := marked_actual_cross_moment_progressions (e j) (e k) (he j) (he k)
          (hcross j k hjk) c A hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
        simpa only [H, M, markedVarianceValue, markedVarianceModel, markedVariancePairModel,
          ite_eq_right hjk, w, μ, ν, P, W] using h
  have hlin := markedProgressionDiscrepancy_linear_all_log Finset.univ b M H Φ T c A
    (1 + 2 / v + 1 / v ^ 2) hb (fun q _ => herror q)
  apply hlin.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hmean] with x hx
  have hm : ∀ j, μ x j ≠ 0 := fun j => (hv.trans_le (hx j)).ne'
  have hw : (fun u => ∑ q, b x q * H x q u) = markedArrayVarianceWeight (P x) (W x) := by
    funext u
    exact markedVarianceFamily_value (fun j => w x j u) (μ x)
  have hmodel : (∑ q, b x q * M x q) = independentArraysVariance (P x) (W x) := by
    rw [independentArraysVariance_eq (P x) (W x) hJ hm]
    exact markedVarianceFamily_model (μ x) (ν x) hm hJ
  rw [hw, hmodel]

end ArtinMatthews
