module

public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-!
# The first good-state test in the determinant lift

PD §3.2 excludes root ratios `r` for which `‖l D r‖ ≤ ε` for one omission
product `D` and one small positive integer `l`. Multiplication by a nonzero
integer preserves Haar measure on the circle. This gives the actual exceptional
set measure, uniformly in all omission products, by a finite union bound.
-/

noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal

namespace ArtinMatthews

/-- One bad rational-root test on the circle of circumference one. -/
def markedBadRootMultiple (q : ℤ) (ε : ℝ) : Set (AddCircle (1 : ℝ)) :=
  {r | ‖q • r‖ ≤ ε}

theorem markedBadRootMultiple_measure (q : ℤ) (hq : q ≠ 0) (ε : ℝ) :
    volume (markedBadRootMultiple q ε) = ENNReal.ofReal (min 1 (2 * ε)) := by
  have hpres := Measure.measurePreserving_zsmul (volume : Measure (AddCircle (1 : ℝ))) hq
  have hset : markedBadRootMultiple q ε =
      (fun r : AddCircle (1 : ℝ) => q • r) ⁻¹' closedBall 0 ε := by
    ext r
    simp [markedBadRootMultiple, mem_closedBall, dist_zero_right]
  rw [hset, hpres.measure_preimage measurableSet_closedBall.nullMeasurableSet,
    AddCircle.volume_closedBall]

theorem markedBadRootMultiple_measure_le (q : ℤ) (hq : q ≠ 0) (ε : ℝ) :
    volume (markedBadRootMultiple q ε) ≤ ENNReal.ofReal (2 * ε) := by
  rw [markedBadRootMultiple_measure q hq]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- Bad ratios for an explicitly indexed family of positive omission products. -/
def markedFirstBadRoots {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (L : ℕ) (ε : ℝ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ i, ⋃ l ∈ Finset.Icc 1 L, markedBadRootMultiple ((D i * l : ℕ) : ℤ) ε

/-- The first good-state exceptional set has measure at most
`2 * (# omission choices) * L * ε`, independent of the sizes of the products. -/
theorem markedFirstBadRoots_measure_le {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (hD : ∀ i, 0 < D i) (L : ℕ) (ε : ℝ) :
    volume (markedFirstBadRoots D L ε) ≤
      (Fintype.card ι : ℝ≥0∞) * L * ENNReal.ofReal (2 * ε) := by
  classical
  apply (measure_iUnion_fintype_le volume _).trans
  calc
    (∑ i, volume (⋃ l ∈ Finset.Icc 1 L,
        markedBadRootMultiple ((D i * l : ℕ) : ℤ) ε)) ≤
        ∑ _i : ι, (L : ℝ≥0∞) * ENNReal.ofReal (2 * ε) := by
      apply Finset.sum_le_sum
      intro i _
      apply (measure_biUnion_finset_le (Finset.Icc 1 L) _).trans
      calc
        (∑ l ∈ Finset.Icc 1 L,
            volume (markedBadRootMultiple ((D i * l : ℕ) : ℤ) ε)) ≤
            ∑ _l ∈ Finset.Icc 1 L, ENNReal.ofReal (2 * ε) := by
          apply Finset.sum_le_sum
          intro l hl
          apply markedBadRootMultiple_measure_le
          exact_mod_cast (Nat.mul_pos (hD i) (Finset.mem_Icc.mp hl).1).ne'
        _ = (L : ℝ≥0∞) * ENNReal.ofReal (2 * ε) := by simp
    _ = _ := by simp [mul_assoc]

/-- Real-valued form of the first good-state exceptional-set estimate. -/
theorem markedFirstBadRoots_real_measure_le {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (hD : ∀ i, 0 < D i) (L : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    volume.real (markedFirstBadRoots D L ε) ≤
      2 * Fintype.card ι * L * ε := by
  have h := markedFirstBadRoots_measure_le D hD L ε
  have hfin : (Fintype.card ι : ℝ≥0∞) * L * ENNReal.ofReal (2 * ε) ≠ ⊤ := by finiteness
  have ht := ENNReal.toReal_mono hfin h
  have ht' : volume.real (markedFirstBadRoots D L ε) ≤
      (Fintype.card ι : ℝ) * L * (2 * ε) := by
    simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε] using ht
  nlinarith

/-- The number of omission tuples for `K` groups with `M` choices in each is
exactly `M^K`, giving the explicit first good-state bound used in PD. -/
theorem markedOmissionFirstBadRoots_real_measure_le (K M L : ℕ)
    (D : (Fin K → Fin M) → ℕ) (hD : ∀ i, 0 < D i) {ε : ℝ} (hε : 0 ≤ ε) :
    volume.real (markedFirstBadRoots D L ε) ≤ 2 * (M : ℝ) ^ K * L * ε := by
  simpa using markedFirstBadRoots_real_measure_le D hD L hε

/-- With the paper's first-test parameters, the exceptional measure is at most
`2 * (# omission choices) * Y^(-1/2)`. This is the explicit union-bound estimate
in the proof of PD Lemma 3.2. -/
theorem markedFirstBadRoots_parameter_bound {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (hD : ∀ i, 0 < D i) {Y : ℝ} (hY : 0 < Y) :
    volume.real (markedFirstBadRoots D ⌊Y ^ (1 / 5 : ℝ)⌋₊ (Y ^ (-7 / 10 : ℝ))) ≤
      2 * Fintype.card ι * Y ^ (-1 / 2 : ℝ) := by
  have hε : 0 ≤ Y ^ (-7 / 10 : ℝ) := Real.rpow_nonneg hY.le _
  apply (markedFirstBadRoots_real_measure_le D hD _ hε).trans
  calc
    2 * Fintype.card ι * (⌊Y ^ (1 / 5 : ℝ)⌋₊ : ℝ) * Y ^ (-7 / 10 : ℝ) ≤
        2 * Fintype.card ι * Y ^ (1 / 5 : ℝ) * Y ^ (-7 / 10 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hε
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hY.le _))
        (by positivity)
    _ = 2 * Fintype.card ι * Y ^ (-1 / 2 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hY]
      norm_num

/-- The bound specialized to one omitted slot in each of `K` groups of size `M`. -/
theorem markedOmissionFirstBadRoots_parameter_bound (K M : ℕ)
    (D : (Fin K → Fin M) → ℕ) (hD : ∀ i, 0 < D i) {Y : ℝ} (hY : 0 < Y) :
    volume.real (markedFirstBadRoots D ⌊Y ^ (1 / 5 : ℝ)⌋₊ (Y ^ (-7 / 10 : ℝ))) ≤
      2 * (M : ℝ) ^ K * Y ^ (-1 / 2 : ℝ) := by
  simpa using markedFirstBadRoots_parameter_bound D hD hY

/-- The growing number `M = J+1` of slots per group in the moment argument. -/
def markedPadSlots (x : ℝ) : ℕ := ⌊(Real.log x) ^ (1 / 100 : ℝ)⌋₊ + 1

theorem markedPadSlots_pow_le (K : ℕ) {x : ℝ} (hx : 1 ≤ Real.log x) :
    (markedPadSlots x : ℝ) ^ K ≤ (2 : ℝ) ^ K * (Real.log x) ^ ((K : ℝ) / 100) := by
  have hx0 : 0 < Real.log x := by linarith
  have hpow : 1 ≤ (Real.log x) ^ (1 / 100 : ℝ) :=
    Real.one_le_rpow hx (by norm_num)
  have hslots : (markedPadSlots x : ℝ) ≤ 2 * (Real.log x) ^ (1 / 100 : ℝ) := by
    have hf := Nat.floor_le (Real.rpow_nonneg hx0.le (1 / 100 : ℝ))
    unfold markedPadSlots
    push_cast
    linarith
  calc
    (markedPadSlots x : ℝ) ^ K ≤ (2 * (Real.log x) ^ (1 / 100 : ℝ)) ^ K :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hslots K
    _ = (2 : ℝ) ^ K * (Real.log x) ^ ((K : ℝ) / 100) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
      congr 2
      ring

/-- The first good-state error at the least permitted exponential label scale. -/
noncomputable def markedFirstGoodError (K : ℕ) (c : ℝ)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ) (x : ℝ) : ℝ :=
  let Y := Real.exp (c * (Real.log x) ^ (1 / 10 : ℝ))
  volume.real (markedFirstBadRoots (D x) ⌊Y ^ (1 / 5 : ℝ)⌋₊ (Y ^ (-7 / 10 : ℝ)))

/-- Uniform pointwise bound for arbitrary positive omission products. The
only polynomial loss is the explicit `M^K` count of omission choices. -/
theorem markedFirstGoodError_le (K : ℕ) (c : ℝ)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ)
    (hD : ∀ x i, 0 < D x i) {x : ℝ} (hx : 1 ≤ Real.log x) :
    markedFirstGoodError K c D x ≤
      2 ^ (K + 1) * (Real.log x) ^ ((K : ℝ) / 100) *
        Real.exp (-(c / 2) * (Real.log x) ^ (1 / 10 : ℝ)) := by
  have h := markedOmissionFirstBadRoots_parameter_bound K (markedPadSlots x)
    (D x) (hD x) (Real.exp_pos (c * (Real.log x) ^ (1 / 10 : ℝ)))
  change markedFirstGoodError K c D x ≤ _ at h
  have hexp : (Real.exp (c * (Real.log x) ^ (1 / 10 : ℝ))) ^ (-1 / 2 : ℝ) =
      Real.exp (-(c / 2) * (Real.log x) ^ (1 / 10 : ℝ)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hexp] at h
  apply h.trans
  calc
    2 * (markedPadSlots x : ℝ) ^ K *
        Real.exp (-(c / 2) * (Real.log x) ^ (1 / 10 : ℝ)) ≤
        2 * (2 ^ K * (Real.log x) ^ ((K : ℝ) / 100)) *
          Real.exp (-(c / 2) * (Real.log x) ^ (1 / 10 : ℝ)) := by
      gcongr
      exact markedPadSlots_pow_le K hx
    _ = _ := by rw [pow_succ]; ring

/-- For every fixed `K`, the actual first good-state exceptional measure saves
every fixed power of `log x`, uniformly over all positive omission products. -/
theorem markedFirstGoodError_log_saving (K : ℕ) {c : ℝ} (hc : 0 < c)
    (D : (x : ℝ) → (Fin K → Fin (markedPadSlots x)) → ℕ)
    (hD : ∀ x i, 0 < D x i) (A : ℝ) :
    Filter.Tendsto (fun x : ℝ => (Real.log x) ^ A * markedFirstGoodError K c D x)
      Filter.atTop (nhds 0) := by
  have hdecay := ((rpow_mul_exp_neg_rpow_tendsto (A + (K : ℝ) / 100)
    (by norm_num : (0 : ℝ) < 1 / 10) (by linarith : 0 < c / 2)).comp
      Real.tendsto_log_atTop).const_mul (2 ^ (K + 1))
  simp only [Function.comp_def, mul_zero] at hdecay
  apply squeeze_zero' _ _ hdecay
  · filter_upwards [Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with x hx
    exact mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Real.log x) A)
      ENNReal.toReal_nonneg
  · filter_upwards [Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with x hx
    have h := mul_le_mul_of_nonneg_left (markedFirstGoodError_le K c D hD hx)
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log x) A)
    convert h using 1
    rw [Real.rpow_add (by linarith : 0 < Real.log x)]
    ring

end ArtinMatthews
