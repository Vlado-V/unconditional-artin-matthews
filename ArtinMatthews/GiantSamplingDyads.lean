module

public import ArtinMatthews.GiantSamplingCofactors
public import Mathlib.Data.Nat.Log


set_option backward.privateInPublic true
@[expose] public section

/-! Exact active cofactor support and disjoint dyadic boxes, with the
actual number of boxes bounded by the logarithm of the cutoff. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def giantSamplingActiveCofactors (x ε : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊2 * x ^ ε⌋₊).filter (fun k : ℕ => x ^ (ε / 2) < (k : ℝ))

theorem mem_giantSamplingActiveCofactors {x ε : ℝ} {k : ℕ} (hx : 0 ≤ x) :
    k ∈ giantSamplingActiveCofactors x ε ↔
      0 < k ∧ x ^ (ε / 2) < (k : ℝ) ∧ (k : ℝ) ≤ 2 * x ^ ε := by
  have hnonneg : 0 ≤ 2 * x ^ ε := mul_nonneg (by norm_num) (Real.rpow_nonneg hx _)
  simp only [giantSamplingActiveCofactors, Finset.mem_filter, Finset.mem_Icc,
    Nat.le_floor_iff hnonneg]
  exact ⟨fun ⟨⟨hpos, hhi⟩, hlo⟩ => ⟨hpos, hlo, hhi⟩,
    fun ⟨hpos, hlo, hhi⟩ => ⟨⟨hpos, hhi⟩, hlo⟩⟩

theorem giantCubicSamplingGiantSum_eq_activeCofactors (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (r : ℕ)
    {ε x : ℝ} (hx : 0 < x) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hH : ∀ ℓ ∈ giantPrimeWindow x ε, ∀ k, H (ℓ * k) = H k) :
    giantCubicSamplingGiantSum η χ H Φ ε x r =
      giantCubicSamplingCofactorSum η χ H Φ ε x r (giantSamplingActiveCofactors x ε) := by
  rw [giantCubicSamplingGiantSum_eq_cofactors η χ H Φ r hx hs hH]
  unfold giantCubicSamplingCofactorSum giantSamplingActiveCofactors
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : x ^ (ε / 2) < (k : ℝ)
  · simp only [hk, ite_true]
  · have hzero : Φ (((ℓ * k : ℕ) : ℝ) / x) = 0 := by
      by_contra hn
      apply hk
      apply giantSampling_cofactor_lower hx hℓ
      simpa only [Nat.cast_mul, one_mul] using (lt_div_iff₀ hx).mp (hs hn).1
    simp only [Nat.cast_mul] at hzero
    simp [hk, giantCubicSamplingKernel, hzero]

def giantSamplingDyadIndices (K : Finset ℕ) : Finset ℕ := K.image (Nat.log 2)

def giantSamplingDyadCofactors (K : Finset ℕ) (i : ℕ) : Finset ℕ :=
  K.filter (fun k => Nat.log 2 k = i)

theorem giantCubicSamplingCofactorSum_eq_dyads (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ)
    (r : ℕ) (K : Finset ℕ) :
    giantCubicSamplingCofactorSum η χ H Φ ε x r K =
      ∑ i ∈ giantSamplingDyadIndices K,
        giantCubicSamplingCofactorSum η χ H Φ ε x r (giantSamplingDyadCofactors K i) := by
  unfold giantCubicSamplingCofactorSum giantSamplingDyadCofactors giantSamplingDyadIndices
  rw [Finset.sum_comm (s := K.image (Nat.log 2)) (t := giantPrimeWindow x ε)]
  apply Finset.sum_congr rfl
  intro ℓ _hℓ
  exact (Finset.sum_fiberwise_of_maps_to (g := Nat.log 2)
    (fun _ hk => Finset.mem_image_of_mem _ hk)
    (fun k => H k * giantCubicSamplingKernel η χ Φ x r (ℓ * k))).symm

theorem giantSampling_dyad_cofactor_bounds {K : Finset ℕ} {i k : ℕ}
    (hk : k ∈ giantSamplingDyadCofactors K i) (hpos : 0 < k) :
    ((2 ^ i : ℕ) : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) < 2 * ((2 ^ i : ℕ) : ℝ) := by
  have hlog := (Finset.mem_filter.mp hk).2
  constructor
  · exact_mod_cast (hlog ▸ Nat.pow_log_le_self 2 hpos.ne')
  · have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
    rw [hlog, Nat.succ_eq_add_one, pow_succ, mul_comm] at hhi
    exact_mod_cast hhi

theorem giantSampling_active_dyad_bounds {x ε : ℝ} (hx : 0 ≤ x) {i : ℕ}
    (hi : i ∈ giantSamplingDyadIndices (giantSamplingActiveCofactors x ε)) :
    let T := ((2 ^ i : ℕ) : ℝ)
    x ^ (ε / 2) / 2 ≤ T ∧ T ≤ 2 * x ^ ε ∧
      ∀ k ∈ giantSamplingDyadCofactors (giantSamplingActiveCofactors x ε) i,
        T ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * T := by
  obtain ⟨k, hk, hlog⟩ := Finset.mem_image.mp hi
  have hrow : k ∈ giantSamplingDyadCofactors (giantSamplingActiveCofactors x ε) i :=
    Finset.mem_filter.mpr ⟨hk, hlog⟩
  have hsupport := (mem_giantSamplingActiveCofactors hx).mp hk
  have hbox := giantSampling_dyad_cofactor_bounds hrow hsupport.1
  refine ⟨by linarith [hsupport.2.1, hbox.2], hbox.1.trans hsupport.2.2, ?_⟩
  intro a ha
  have hpos := ((mem_giantSamplingActiveCofactors hx).mp (Finset.mem_filter.mp ha).1).1
  exact ⟨(giantSampling_dyad_cofactor_bounds ha hpos).1,
    (giantSampling_dyad_cofactor_bounds ha hpos).2.le⟩

theorem giantSampling_active_dyad_card_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    ((giantSamplingDyadIndices (giantSamplingActiveCofactors x ε)).card : ℝ) ≤
      2 + (ε / Real.log 2) * Real.log x := by
  let B := ⌊2 * x ^ ε⌋₊
  let N := Nat.log 2 B
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hB : 0 < B := (Nat.one_le_floor_iff _).mpr (by linarith [Real.one_le_rpow hx hε])
  have hsub : giantSamplingDyadIndices (giantSamplingActiveCofactors x ε) ⊆
      Finset.range (N + 1) := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    have hkB : k ≤ B := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hkB))
  have hpow : (2 : ℝ) ^ N ≤ 2 * x ^ ε := by
    exact (show (2 : ℝ) ^ N ≤ (B : ℝ) from by exact_mod_cast Nat.pow_log_le_self 2 hB.ne').trans
      (Nat.floor_le (by positivity))
  have hlog := Real.log_le_log (pow_pos (by norm_num) N) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx₀ ε).ne',
    Real.log_rpow hx₀] at hlog
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := (le_div_iff₀ hlog₂).mpr hlog
  calc
    _ ≤ (N : ℝ) + 1 := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    _ ≤ (Real.log 2 + ε * Real.log x) / Real.log 2 + 1 := add_le_add hn le_rfl
    _ = _ := by field_simp; ring

end ArtinMatthews
