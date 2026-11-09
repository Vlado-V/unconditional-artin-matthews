module

public import ArtinMatthews.MarkedTypeIIGoodFirst
public import Mathlib.MeasureTheory.Integral.Bochner.Set


set_option backward.privateInPublic true
@[expose] public section

/-!
# Pair separation in the second determinant good-state test

For distinct integer trial values `u,v` and a nonzero fresh product `T`, the
map `r ↦ (u-v) T r` preserves circle measure. The pair union bound and finite
averaging therefore give the actual second-test exceptional probability and
its Markov estimate. No root-lift or operator moment estimate is assumed.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal

namespace ArtinMatthews

theorem measurableSet_markedBadRootMultiple (q : ℤ) (ε : ℝ) :
    MeasurableSet (markedBadRootMultiple q ε) := by
  have hm : Measurable (fun r : AddCircle (1 : ℝ) => q • r) := by fun_prop
  have hs : MeasurableSet (closedBall (0 : AddCircle (1 : ℝ)) ε) := measurableSet_closedBall
  convert hs.preimage hm using 1
  ext r
  simp [markedBadRootMultiple, mem_closedBall, dist_zero_right]

/-- A root ratio is bad if two distinct integer trial values become too close. -/
def markedPairBadRoots (Q : Finset ℤ) (T : ℤ) (ε : ℝ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ u ∈ Q, ⋃ v ∈ Q, if u = v then ∅ else markedBadRootMultiple ((u - v) * T) ε

theorem measurableSet_markedPairBadRoots (Q : Finset ℤ) (T : ℤ) (ε : ℝ) :
    MeasurableSet (markedPairBadRoots Q T ε) := by
  classical
  unfold markedPairBadRoots
  apply Finset.measurableSet_biUnion
  intro u _
  apply Finset.measurableSet_biUnion
  intro v _
  split_ifs
  · exact MeasurableSet.empty
  · exact measurableSet_markedBadRootMultiple _ _

/-- Pair separation failure has measure at most `2 |Q|² ε`, uniformly in the
nonzero integer fresh product `T`. -/
theorem markedPairBadRoots_measure_le (Q : Finset ℤ) {T : ℤ} (hT : T ≠ 0) (ε : ℝ) :
    volume (markedPairBadRoots Q T ε) ≤
      (Q.card : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * ε) := by
  classical
  apply (measure_biUnion_finset_le Q _).trans
  calc
    (∑ u ∈ Q, volume (⋃ v ∈ Q,
        if u = v then ∅ else markedBadRootMultiple ((u - v) * T) ε)) ≤
        ∑ _u ∈ Q, (Q.card : ℝ≥0∞) * ENNReal.ofReal (2 * ε) := by
      apply Finset.sum_le_sum
      intro u _
      apply (measure_biUnion_finset_le Q _).trans
      calc
        (∑ v ∈ Q, volume (if u = v then ∅ else markedBadRootMultiple ((u - v) * T) ε)) ≤
            ∑ _v ∈ Q, ENNReal.ofReal (2 * ε) := by
          apply Finset.sum_le_sum
          intro v _
          by_cases huv : u = v
          · simp [huv]
          · simp only [huv, ↓reduceIte]
            exact markedBadRootMultiple_measure_le _ (mul_ne_zero (sub_ne_zero.mpr huv) hT) ε
        _ = _ := by simp
    _ = _ := by simp [pow_two, mul_assoc]

theorem markedPairBadRoots_real_measure_le (Q : Finset ℤ) {T : ℤ} (hT : T ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    volume.real (markedPairBadRoots Q T ε) ≤ 2 * (Q.card : ℝ) ^ 2 * ε := by
  have h := ENNReal.toReal_mono (by finiteness :
      (Q.card : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * ε) ≠ ⊤)
    (markedPairBadRoots_measure_le Q hT ε)
  have h' : volume.real (markedPairBadRoots Q T ε) ≤ (Q.card : ℝ) ^ 2 * (2 * ε) := by
    simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε] using h
  nlinarith

/-- Probability of pair failure when the fresh product is drawn from a finite law. -/
def markedPairFailureProbability {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (ε : ℝ) (r : AddCircle (1 : ℝ)) : ℝ := by
  classical
  exact ∑ i, if r ∈ markedPairBadRoots Q (T i) ε then w i else 0

theorem markedPairFailureProbability_nonneg {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ε : ℝ) (r : AddCircle (1 : ℝ)) :
    0 ≤ markedPairFailureProbability Q T w ε r := by
  classical
  unfold markedPairFailureProbability
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hw i
  · exact le_rfl

theorem markedPairFailureProbability_integrable {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (w : ι → ℝ) (ε : ℝ) :
    Integrable (markedPairFailureProbability Q T w ε) volume := by
  apply integrable_finsetSum
  intro i _
  change Integrable ((markedPairBadRoots Q (T i) ε).indicator (fun _ => w i)) volume
  exact (integrable_const _).indicator (measurableSet_markedPairBadRoots Q (T i) ε)

/-- Finite averaging over the fresh labels costs no extra factor. -/
theorem markedPairFailureProbability_integral_le {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (hT : ∀ i, T i ≠ 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ r, markedPairFailureProbability Q T w ε r) ≤ 2 * (Q.card : ℝ) ^ 2 * ε := by
  classical
  have hi (i : ι) : Integrable ((markedPairBadRoots Q (T i) ε).indicator (fun _ => w i)) volume :=
    (integrable_const _).indicator (measurableSet_markedPairBadRoots Q (T i) ε)
  unfold markedPairFailureProbability
  change (∫ r : AddCircle (1 : ℝ), ∑ i,
    (markedPairBadRoots Q (T i) ε).indicator (fun _ => w i) r) ≤ _
  rw [integral_finsetSum _ (fun i _ => hi i)]
  calc
    (∑ i, ∫ r : AddCircle (1 : ℝ), (markedPairBadRoots Q (T i) ε).indicator (fun _ => w i) r) =
        ∑ i, volume.real (markedPairBadRoots Q (T i) ε) * w i := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_const (w i) (measurableSet_markedPairBadRoots Q (T i) ε)
    _ ≤ ∑ i, (2 * (Q.card : ℝ) ^ 2 * ε) * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (markedPairBadRoots_real_measure_le Q (hT i) hε) (hw i)
    _ = _ := by rw [← Finset.mul_sum, hwsum, mul_one]

/-- Markov's inequality gives the second-test exceptional set at any positive
probability threshold, with the explicit pair count. -/
theorem markedPairFailureProbability_exceptional_le {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (hT : ∀ i, T i ≠ 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 < η) :
    volume.real {r | η ≤ markedPairFailureProbability Q T w ε r} ≤
      (2 * (Q.card : ℝ) ^ 2 * ε) / η := by
  apply (le_div_iff₀ hη).mpr
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (markedPairFailureProbability_nonneg Q T w hw ε))
    (markedPairFailureProbability_integrable Q T w ε) η
  calc
    volume.real {r | η ≤ markedPairFailureProbability Q T w ε r} * η =
        η * volume.real {r | η ≤ markedPairFailureProbability Q T w ε r} := mul_comm _ _
    _ ≤ _ := hmarkov
    _ ≤ _ := markedPairFailureProbability_integral_le Q T hT w hw hwsum hε

/-- The exponential separation scale and probability threshold in PD's second
good-state test give the explicit bound `200 |Q|² exp(-3t/4)`. -/
theorem markedSecondGood_parameter_bound {ι : Type*} [Fintype ι]
    (Q : Finset ℤ) (T : ι → ℤ) (hT : ∀ i, T i ≠ 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) (t : ℝ) :
    volume.real {r | Real.exp (-t / 4) ≤
      markedPairFailureProbability Q T w (100 * Real.exp (-t)) r} ≤
      200 * (Q.card : ℝ) ^ 2 * Real.exp (-3 * t / 4) := by
  apply (markedPairFailureProbability_exceptional_le Q T hT w hw hwsum
    (by positivity : 0 ≤ 100 * Real.exp (-t)) (Real.exp_pos (-t / 4))).trans_eq
  have hexp : Real.exp (-t) / Real.exp (-t / 4) = Real.exp (-3 * t / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    (2 * (Q.card : ℝ) ^ 2 * (100 * Real.exp (-t))) / Real.exp (-t / 4) =
        200 * (Q.card : ℝ) ^ 2 * (Real.exp (-t) / Real.exp (-t / 4)) := by ring
    _ = _ := by rw [hexp]

end ArtinMatthews
