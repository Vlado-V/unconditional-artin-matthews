module

public import ArtinMatthews.SourceReflectionDyadicLoss
public import Mathlib.Data.Nat.Log


set_option backward.privateInPublic true
@[expose] public section

/-! Exact norm dyads and summation over the nonempty dyads in Section 04. -/
namespace ArtinMatthews.SourceEulerAssembly
open scoped Classical BigOperators
noncomputable section

def sourceReflectionDyadLength (X : ℝ) : ℕ := Nat.log 2 ⌊X⌋₊ + 1

theorem sourceReflectionDyad_bounds {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) ^ Nat.log 2 n ≤ n ∧ (n : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 n := by
  constructor
  · exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  · have h : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
    simpa only [pow_succ, mul_comm] using h

theorem sourceReflectionDyad_lt_length {n : ℕ} {X : ℝ} (hn : (n : ℝ) ≤ X) :
    Nat.log 2 n < sourceReflectionDyadLength X :=
  Nat.lt_succ_of_le (Nat.log_mono_right (Nat.le_floor hn))

theorem sourceReflectionDyadLength_le_log {X : ℝ} (hX : 1 ≤ X) :
    (sourceReflectionDyadLength X : ℝ) ≤ Real.log (2 * X) / Real.log 2 := by
  have hx := zero_lt_one.trans_le hX
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hpow : (2 : ℝ) ^ Nat.log 2 ⌊X⌋₊ ≤ X := by
    apply le_trans _ (Nat.floor_le hx.le)
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp hfloor)
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 ⌊X⌋₊) hpow
  rw [Real.log_pow] at hl
  rw [sourceReflectionDyadLength, Nat.cast_add, Nat.cast_one, le_div_iff₀ hlog,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne']
  linarith

theorem sourceReflectionDyadPairs_card_le {ι : Type*} (A : Finset ι) (p d : ι → ℕ)
    {X : ℝ} (hX : ∀ i ∈ A, 0 < p i ∧ 0 < d i ∧ (p i : ℝ) * d i ≤ X) :
    (A.image (fun i => (Nat.log 2 (p i), Nat.log 2 (d i)))).card ≤
      sourceReflectionDyadLength X ^ 2 := by
  let B := Finset.range (sourceReflectionDyadLength X)
  have hsub : A.image (fun i => (Nat.log 2 (p i), Nat.log 2 (d i))) ⊆ B ×ˢ B := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hp, hd, hb⟩ := hX i hi
    have hp₁ : (1 : ℝ) ≤ p i := by exact_mod_cast hp
    have hd₁ : (1 : ℝ) ≤ d i := by exact_mod_cast hd
    have hpX : (p i : ℝ) ≤ X := by
      refine (le_mul_of_one_le_right (Nat.cast_nonneg _) hd₁).trans hb
    have hdX : (d i : ℝ) ≤ X := by
      refine (le_mul_of_one_le_left (Nat.cast_nonneg _) hp₁).trans hb
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (sourceReflectionDyad_lt_length hpX),
      Finset.mem_range.mpr (sourceReflectionDyad_lt_length hdX)⟩
  simpa only [Finset.card_product, Finset.card_range, pow_two, B] using Finset.card_le_card hsub

theorem sourceReflectionSumDyadicBounds {K M ε : ℝ} (hK : 1 ≤ K)
    (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z → ∀ {ι : Type} (A : Finset ι)
      (p d : ι → ℕ) (w : ι → ℝ) (B : ℝ), 0 ≤ B →
      (∀ i ∈ A, 0 < p i ∧ 0 < d i ∧ (p i : ℝ) * d i ≤ K * Z ^ M) →
      (∀ j k : ℕ, ∑ i ∈ A.filter (fun i => (Nat.log 2 (p i), Nat.log 2 (d i)) = (j,k)), w i ≤
        B * Z ^ (ε / 2) * Real.sqrt ((2 : ℝ) ^ j) *
          ((2 : ℝ) ^ k + ((2 : ℝ) ^ k) ^ 2 * (2 : ℝ) ^ j / Z)) →
      ∑ i ∈ A, w i ≤ C * B * Z ^ (2 * M - 1 + ε) := by
  have hk₂ : 1 ≤ 2 * K := by linarith
  obtain ⟨H, hH, hlog⟩ := sourceReflectionLogPower_le hk₂ (zero_le_one.trans hM)
    (show 0 < ε / 2 by positivity) 2 (by decide)
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C := H / Real.log 2 ^ 2 * (K + K ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Z hZ ι A p d w B hB hA hb
  let bins := A.image (fun i => (Nat.log 2 (p i), Nat.log 2 (d i)))
  let X := K * Z ^ M
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hZ (zero_le_one.trans hM))
  have hz := zero_lt_one.trans_le hZ
  have hc : (bins.card : ℝ) ≤ (H / Real.log 2 ^ 2) * Z ^ (ε / 2) := by
    have h := sourceReflectionDyadPairs_card_le A p d hA
    have h' : (bins.card : ℝ) ≤ (sourceReflectionDyadLength X : ℝ) ^ 2 := by exact_mod_cast h
    refine h'.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) (sourceReflectionDyadLength_le_log hX) 2).trans ?_)
    rw [div_pow, div_mul_eq_mul_div, show 2 * X = (2 * K) * Z ^ M by dsimp [X]; ring]
    exact div_le_div_of_nonneg_right (hlog Z hZ) (sq_nonneg _)
  have hbin (j : ℕ × ℕ) (hj : j ∈ bins) :
      ∑ i ∈ A.filter (fun i => (Nat.log 2 (p i), Nat.log 2 (d i)) = j), w i ≤
        B * Z ^ (ε / 2) * ((K + K ^ 2) * Z ^ (2 * M - 1)) := by
    let P := (2 : ℝ) ^ j.1
    let D := (2 : ℝ) ^ j.2
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hj
    obtain ⟨hp, hd, hpd⟩ := hA i hi
    have hp' : P ≤ p i := by
      change (2 : ℝ) ^ j.1 ≤ p i
      rw [← congrArg Prod.fst he]
      exact (sourceReflectionDyad_bounds hp).1
    have hd' : D ≤ d i := by
      change (2 : ℝ) ^ j.2 ≤ d i
      rw [← congrArg Prod.snd he]
      exact (sourceReflectionDyad_bounds hd).1
    have hPD : P * D ≤ X :=
      (mul_le_mul hp' hd' (by dsimp [D]; positivity) (Nat.cast_nonneg _)).trans hpd
    have hP : 1 ≤ P := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hD : 1 ≤ D := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    calc
      _ ≤ B * Z ^ (ε / 2) * Real.sqrt P * (D + D ^ 2 * P / Z) := hb j.1 j.2
      _ = B * Z ^ (ε / 2) * (Real.sqrt P * (D + D ^ 2 * P / Z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sourceReflectionMainScale_le hZ hK hM hP hD hPD) (by positivity)
  calc
    _ = ∑ j ∈ bins, ∑ i ∈ A.filter (fun i => (Nat.log 2 (p i), Nat.log 2 (d i)) = j), w i := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) w
    _ ≤ ∑ _j ∈ bins, B * Z ^ (ε / 2) * ((K + K ^ 2) * Z ^ (2 * M - 1)) :=
      Finset.sum_le_sum hbin
    _ = (bins.card : ℝ) * (B * Z ^ (ε / 2) * ((K + K ^ 2) * Z ^ (2 * M - 1))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H / Real.log 2 ^ 2 * Z ^ (ε / 2)) *
        (B * Z ^ (ε / 2) * ((K + K ^ 2) * Z ^ (2 * M - 1))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      rw [show 2 * M - 1 + ε = ε / 2 + ε / 2 + (2 * M - 1) by ring,
        Real.rpow_add hz, Real.rpow_add hz]
      dsimp [C]
      ring

end
end ArtinMatthews.SourceEulerAssembly
