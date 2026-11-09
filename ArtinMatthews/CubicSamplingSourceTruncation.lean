module

public import ArtinMatthews.CubicSamplingArrayLevel
public import ArtinMatthews.MarkedArrayBandStructure
public import ArtinMatthews.MarkedProgressionGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Section 6.3 prime bands and the literal floor depth. The retained
divisor level and indexed coefficient mass are both subpolynomial. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def cubicSamplingTruncationDepth (x : ℝ) : ℕ := ⌊(Real.log x) ^ (1 / 100 : ℝ)⌋₊

theorem cubicSampling_actualArray_retained_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    (a : J → ℕ) (ha : ∀ j, 0 < a j) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      (∀ u, |(∏ j, (bandWeight (P j) (V j) u) ^ a j) -
        cubicSamplingArrayTruncation P V a k u| ≤ cubicSamplingArrayTail P V a (k + 1) u) ∧
      (∀ t ∈ representedArrayChoices P a,
        ∀ i ∈ markedWeightedIndices (Finset.univ.biUnion P) (representedArraySelected t) k,
          0 < markedWeightedDivisor (representedArraySelected t) i ∧
          Squarefree (markedWeightedDivisor (representedArraySelected t) i) ∧
          (markedWeightedDivisor (representedArraySelected t) i : ℝ) ≤ x ^ γ) ∧
      (∑ t ∈ representedArrayChoices P a,
        ∑ i ∈ markedWeightedIndices (Finset.univ.biUnion P) (representedArraySelected t) k,
          |representedArrayCoefficient V a t *
            markedWeightedCoefficient (representedArrayDamping Finset.univ P a (1 / 2)) i|) ≤ x ^ γ := by
  let K := ∑ j, a j
  let v := Real.log 2 / 2
  let C := (1 / v) ^ K
  have hv : 0 < v := by dsimp only [v]; positivity
  have hb := marked_actual_band_structure_eventually e (fun j => (he j).1) hinj
    (α := 0) (β := 1 / 5) (fun j => (he j).1.le) (fun j => (he j).2)
  have hg := marked_truncation_power_le_rpow_eventually (1 / 100) (1 / 5) K (γ / 2)
    (by norm_num) (by norm_num) (by norm_num) (half_pos hγ)
  have hc := (tendsto_rpow_atTop (half_pos hγ)).eventually (eventually_ge_atTop C)
  filter_upwards [hb, hg, hc, eventually_ge_atTop (1 : ℝ)] with x hxBand hxGrowth hxC hx
  obtain ⟨hdis, hband, hV, _hmass⟩ := hxBand
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let Z := Real.exp (2 * (Real.log x) ^ (1 / 5 : ℝ))
  have hZ : 1 ≤ Z := Real.one_le_exp
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.log_nonneg hx) _))
  have hP (j : J) (p : ℕ) (hp : p ∈ P j) : p.Prime ∧ (p : ℝ) ≤ Z :=
    ⟨(hband j p hp).1, (hband j p hp).2.2⟩
  have hGrowth : ((k + 1 : ℕ) : ℝ) * Z ^ (k + K) ≤ x ^ (γ / 2) := hxGrowth
  have hpow : Z ^ (k + K) ≤ x ^ γ := by
    calc
      _ ≤ ((k + 1 : ℕ) : ℝ) * Z ^ (k + K) := le_mul_of_one_le_left
        (pow_nonneg (zero_le_one.trans hZ) _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
      _ ≤ x ^ (γ / 2) := hGrowth
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  refine ⟨fun u => cubicSampling_arrayTruncation_error P V a ha (fun j => hv.le.trans (hV j))
    (fun j p hp => (hP j p hp).1) hdis k u, ?_, ?_⟩
  · intro t ht i hi
    obtain ⟨hp, hs, hb⟩ := cubicSampling_retainedDivisor_level P a hZ hP ht hi
    exact ⟨hp, hs, hb.trans hpow⟩
  · calc
      _ ≤ (Z / v) ^ K * ((k + 1 : ℕ) : ℝ) * Z ^ k :=
        cubicSampling_retainedCoefficient_mass P V a hv hZ hV hP hdis k
      _ = C * (((k + 1 : ℕ) : ℝ) * Z ^ (k + K)) := by
        dsimp only [C]
        rw [div_pow, one_div, inv_pow, pow_add]
        ring
      _ ≤ C * x ^ (γ / 2) := mul_le_mul_of_nonneg_left hGrowth (by dsimp only [C]; positivity)
      _ ≤ x ^ (γ / 2) * x ^ (γ / 2) :=
        mul_le_mul_of_nonneg_right hxC (Real.rpow_nonneg (zero_le_one.trans hx) _)
      _ = x ^ γ := by rw [← Real.rpow_add (zero_lt_one.trans_le hx), add_halves]

end ArtinMatthews
