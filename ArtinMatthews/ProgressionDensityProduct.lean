module

public import ArtinMatthews.ReciprocalTail
public import ArtinMatthews.MarkedEstimateModelBounds
public import ArtinMatthews.MarkedEstimateMertensBands


set_option backward.privateInPublic true
@[expose] public section

/-! Euler-product bounds for the enlarged progression in Section 10.2.
The identification with the number of admissible residue classes is a
separate finite Chinese-remainder calculation. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators

theorem sum_progression_corrections_le_half (P : Finset ℕ)
    (hP : ∀ p ∈ P, 3 < p) :
    (∑ p ∈ P, 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 / 2 := by
  classical
  let Q := P.image (fun p => p - 1)
  have hQ : ∀ q ∈ Q, 2 < q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have := hP p hp
    omega
  have himage : (∑ p ∈ P, 1 / ((p : ℝ) - 1) ^ 2) =
      ∑ q ∈ Q, 1 / (q : ℝ) ^ 2 := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_sub (by have := hP p hp; omega), Nat.cast_one]
    · intro p hp q hq hpq
      have := hP p hp
      have := hP q hq
      dsimp at hpq
      omega
  rw [himage]
  calc
    _ ≤ ∑ q ∈ Q, 1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' : (2 : ℝ) < q := by exact_mod_cast hQ q hq
      apply one_div_le_one_div_of_le (by nlinarith)
      nlinarith
    _ ≤ 1 / (2 : ℝ) := sum_reciprocal_tail_le Q 2 (by norm_num) hQ

theorem progression_correction_product_ge_half (P : Finset ℕ)
    (hP : ∀ p ∈ P, 3 < p) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hs := sum_progression_corrections_le_half P hP
  have hp := one_sub_sum_le_product P (fun p => 1 / ((p : ℝ) - 1) ^ 2) (by
    intro p hp
    have hp' : (3 : ℝ) < p := by exact_mod_cast hP p hp
    exact ⟨by positivity, (div_le_one (sq_pos_of_pos (by linarith))).mpr (by nlinarith)⟩)
  linarith

noncomputable def progressionDensityProduct (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (((p : ℝ) - 2) / ((p : ℝ) - 1))

/-- The exact algebraic factorization used in (10.4). -/
theorem progressionDensityProduct_factor (P : Finset ℕ)
    (hP : ∀ p ∈ P, 3 < p) :
    progressionDensityProduct P =
      (∏ p ∈ P, (1 - 1 / (p : ℝ))) *
        ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' : (3 : ℝ) < p := by exact_mod_cast hP p hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- A uniform comparison independent of which large primes were excluded
because they already divide the initial modulus. -/
theorem progressionDensityProduct_ge_mertens_half (P : Finset ℕ) (N : ℕ)
    (hsub : P ⊆ Nat.primesLE N) (hP : ∀ p ∈ P, 3 < p) :
    (1 / 2 : ℝ) * (∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))) ≤
      progressionDensityProduct P := by
  have hp0 (p : ℕ) (hp : p ∈ Nat.primesLE N) : 0 ≤ 1 - 1 / (p : ℝ) := by
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp')
  have hprod : (∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))) ≤
      ∏ p ∈ P, (1 - 1 / (p : ℝ)) :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hsub hp0
      (fun _ _ _ => sub_le_self _ (by positivity))
  rw [progressionDensityProduct_factor P hP]
  calc
    _ ≤ (1 / 2 : ℝ) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by gcongr
    _ ≤ _ := by
      rw [mul_comm (1 / 2 : ℝ)]
      exact mul_le_mul_of_nonneg_left (progression_correction_product_ge_half P hP)
        (Finset.prod_nonneg (fun p hp => hp0 p (hsub hp)))

noncomputable def progressionDensityLowerConstant : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-1) / 2

theorem progressionDensityLowerConstant_pos : 0 < progressionDensityLowerConstant := by
  unfold progressionDensityLowerConstant
  positivity

/-- The lower bound needed in (10.4) is uniform in every choice of omitted
prime factors, including those already dividing the initial modulus. -/
theorem progressionDensityProduct_log_lower_eventually :
    ∀ᶠ Y : ℝ in atTop, ∀ P : Finset ℕ,
      P ⊆ Nat.primesLE ⌊Y⌋₊ → (∀ p ∈ P, 3 < p) →
      progressionDensityLowerConstant / Real.log Y ≤ progressionDensityProduct P := by
  have hE := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  filter_upwards [hE.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0)),
    eventually_gt_atTop (1 : ℝ)] with Y hE hY
  intro P hP hlarge
  have hset : Nat.primesLE ⌊Y⌋₊ = (Finset.Ioc 0 ⌊Y⌋₊).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hp, hprime⟩
      exact ⟨⟨hprime.pos, hp⟩, hprime⟩
    · rintro ⟨⟨_, hp⟩, hprime⟩
      exact ⟨hp, hprime⟩
  have hfull : (∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 - 1 / (p : ℝ))) =
      Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ Y) / Real.log Y := by
    rw [hset]
    exact Mertens.prod_one_minus_div_prime_eq hY
  calc
    _ = (1 / 2 : ℝ) * (Real.exp (-Real.eulerMascheroniConstant) *
          Real.exp (-1) / Real.log Y) := by unfold progressionDensityLowerConstant; ring
    _ ≤ (1 / 2 : ℝ) * (∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 - 1 / (p : ℝ))) := by
      rw [hfull]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_right _ (Real.log_pos hY).le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE.le) (Real.exp_nonneg _)
    _ ≤ _ := progressionDensityProduct_ge_mertens_half P ⌊Y⌋₊ hP hlarge

/-- This discharges the final choice of a fixed sufficiently large `Y`:
the reciprocal error `B/Y` is smaller than any fixed positive multiple of
the enlarged progression's Euler-product density. -/
theorem exists_cutoff_for_progressionDensityProduct
    (P : ℝ → Finset ℕ) (hP : ∀ Y, P Y ⊆ Nat.primesLE ⌊Y⌋₊)
    (hlarge : ∀ Y, ∀ p ∈ P Y, 3 < p) (B Y₀ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ Y : ℝ, Y₀ < Y ∧ 1 < Y ∧ B / Y < κ * progressionDensityProduct (P Y) := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul B
  simp only [id_eq, mul_zero] at hlim
  have hc : 0 < κ * progressionDensityLowerConstant :=
    mul_pos hκ progressionDensityLowerConstant_pos
  have hsmall : ∀ᶠ Y : ℝ in atTop,
      B * (Real.log Y / Y) < κ * progressionDensityLowerConstant := by
    simpa only [id_eq, mul_zero] using hlim.eventually (gt_mem_nhds hc)
  have hall : ∀ᶠ Y : ℝ in atTop,
      Y₀ < Y ∧ 1 < Y ∧ B / Y < κ * progressionDensityProduct (P Y) := by
    filter_upwards [hsmall, progressionDensityProduct_log_lower_eventually,
      eventually_gt_atTop Y₀, eventually_gt_atTop (1 : ℝ)] with Y hs hl hY₀ hY
    refine ⟨hY₀, hY, ?_⟩
    have hY0 : 0 < Y := by linarith
    have hlog : 0 < Real.log Y := Real.log_pos hY
    have hs' : B * Real.log Y < κ * progressionDensityLowerConstant * Y := by
      apply (div_lt_iff₀ hY0).mp
      simpa only [mul_div_assoc] using hs
    calc
      B / Y < κ * (progressionDensityLowerConstant / Real.log Y) := by
        rw [← mul_div_assoc]
        exact (div_lt_div_iff₀ hY0 hlog).mpr hs'
      _ ≤ _ := mul_le_mul_of_nonneg_left (hl (P Y) (hP Y) (hlarge Y)) hκ.le
  exact hall.exists

end ArtinMatthews

