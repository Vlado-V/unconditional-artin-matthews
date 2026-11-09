module

public import ArtinMatthews.GiantSamplingBilinearRows


set_option backward.privateInPublic true
@[expose] public section

/-! Literal use of the source shifted bilinear estimate on the squarefree
cofactor row. The only analytic input is the coefficient test of (5.1). -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def GiantSamplingShiftedBilinearBound (η : HeckeFamily.Character)
    (Φ : ℝ → ℝ) (x ν Cν : ℝ) : Prop :=
  ∀ lo hi : ℝ, 1 ≤ lo → lo ≤ hi → ∀ (A N : Finset ℕ) (α β : ℕ → ℂ),
    (∀ a ∈ A, Squarefree a ∧ lo ≤ (a : ℝ) ∧ (a : ℝ) ≤ hi) →
    (∀ n ∈ N, 0 < n) →
    (∀ a ∈ A, ‖α a‖ ≤ 1) → (∀ n ∈ N, ‖β n‖ ≤ 1) →
    ‖giantCubicSamplingBilinear η Φ x A N α β‖ ≤
      Cν * x ^ ν * (x * lo ^ (-(1 / 2) : ℝ) + x ^ (7 / 8 : ℝ) * hi ^ (3 / 8 : ℝ))

theorem giantCubicSamplingBilinear_left_mul (η : HeckeFamily.Character)
    (Φ : ℝ → ℝ) (x : ℝ) (A N : Finset ℕ) (α β : ℕ → ℂ) (z : ℂ) :
    giantCubicSamplingBilinear η Φ x A N (fun a => z * α a) β =
      z * giantCubicSamplingBilinear η Φ x A N α β := by
  unfold giantCubicSamplingBilinear
  simp_rw [Finset.mul_sum, mul_assoc]

theorem giantCubicSampling_squareRow_norm_le (η : HeckeFamily.Character)
    {M r : ℕ} [NeZero M] [NeZero r]
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε : ℝ)
    (K : Finset ℕ) (B d : ℕ) (hd : 0 < d)
    {x T C ν Cν : ℝ} (hx : 0 < x) (hT : 0 < T) (hC : 0 < C) (hCν : 0 ≤ Cν)
    (hlo : 1 ≤ T / (d : ℝ) ^ 2)
    (hK : ∀ k ∈ K, T ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * T)
    (hH : ∀ k ∈ K, ‖H k‖ ≤ C)
    (hbilinear : GiantSamplingShiftedBilinearBound η Φ x ν Cν) :
    ‖∑ a ∈ giantSamplingSquarefreeRow K B d, ∑ n ∈ giantSamplingScaledWindow x ε d,
      H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (a * n)‖ ≤
        (r : ℝ) * (M : ℝ) ^ 2 * C * (Cν * x ^ ν *
          (x * (T / (d : ℝ) ^ 2) ^ (-(1 / 2) : ℝ) +
            x ^ (7 / 8 : ℝ) * (2 * T / (d : ℝ) ^ 2) ^ (3 / 8 : ℝ))) := by
  classical
  let A := giantSamplingSquarefreeRow K B d
  let N := giantSamplingScaledWindow x ε d
  let R := (ZMod r)ˣ × ZMod M × ZMod M
  let lo := T / (d : ℝ) ^ 2
  let hi := 2 * T / (d : ℝ) ^ 2
  let Q := Cν * x ^ ν * (x * lo ^ (-(1 / 2) : ℝ) + x ^ (7 / 8 : ℝ) * hi ^ (3 / 8 : ℝ))
  let α (c : R) (a : ℕ) := giantSamplingLeftResidue c.1 c.2.1 (H (d ^ 2 * a)) a
  let β (c : R) (n : ℕ) := giantSamplingRightResidue c.1 c.2.2 n
  have hd₀ : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hlohi : lo ≤ hi := div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hQ : 0 ≤ Q := by
    have hlow : 0 ≤ lo := zero_le_one.trans hlo
    have hhigh : 0 ≤ hi := hlow.trans hlohi
    exact mul_nonneg (mul_nonneg hCν (Real.rpow_nonneg hx.le _))
      (add_nonneg (mul_nonneg hx.le (Real.rpow_nonneg hlow _))
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hhigh _)))
  have hrow (a : ℕ) (ha : a ∈ A) : Squarefree a ∧ lo ≤ (a : ℝ) ∧ (a : ℝ) ≤ hi := by
    obtain ⟨_, hsq, haK⟩ := Finset.mem_filter.mp ha
    refine ⟨hsq, (div_le_iff₀ (pow_pos hd₀ _)).mpr ?_, (le_div_iff₀ (pow_pos hd₀ _)).mpr ?_⟩
    · simpa only [Nat.cast_mul, Nat.cast_pow, mul_comm] using (hK _ haK).1
    · simpa only [Nat.cast_mul, Nat.cast_pow, mul_comm] using (hK _ haK).2
  have hN (n : ℕ) (hn : n ∈ N) : 0 < n := by
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hn
    exact Nat.mul_pos (pow_pos hd _) ((mem_giantPrimeWindow hx.le).mp hℓ).1.pos
  have hα (c : R) (a : ℕ) (ha : a ∈ A) : ‖α c a‖ ≤ C := by
    dsimp only [α, giantSamplingLeftResidue]
    split_ifs
    · exact hH _ (Finset.mem_filter.mp ha).2.2
    · simpa only [norm_zero] using hC.le
  have hβ (c : R) (n : ℕ) : ‖β c n‖ ≤ 1 := by
    dsimp only [β, giantSamplingRightResidue]
    split_ifs <;> simp
  have hscaled (c : R) : ‖giantCubicSamplingBilinear η Φ x A N (α c) (β c)‖ ≤ C * Q := by
    let a := fun k => α c k / (C : ℂ)
    have ha (k : ℕ) (hk : k ∈ A) : ‖a k‖ ≤ 1 := by
      dsimp only [a]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
      exact (div_le_one hC).mpr (hα c k hk)
    have hraw : α c = fun k => (C : ℂ) * a k := by
      funext k
      dsimp only [a]
      field_simp [show (C : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hC.ne']
    have htest := hbilinear lo hi hlo hlohi A N a (β c) hrow hN ha (fun n _ => hβ c n)
    rw [hraw, giantCubicSamplingBilinear_left_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hC]
    exact mul_le_mul_of_nonneg_left htest hC.le
  rw [giantCubicSamplingSquareRow_eq_crt]
  change ‖∑ c : R, χ (c.2.1 * c.2.2 + 1) *
    giantCubicSamplingBilinear η Φ x A N (α c) (β c)‖ ≤ _
  calc
    _ ≤ ∑ c : R, ‖χ (c.2.1 * c.2.2 + 1) * giantCubicSamplingBilinear η Φ x A N (α c) (β c)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c : R, C * Q := by
      apply Finset.sum_le_sum
      intro c _hc
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hscaled c)
    _ = (Fintype.card R : ℝ) * (C * Q) := by simp
    _ ≤ ((r : ℝ) * (M : ℝ) ^ 2) * (C * Q) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC.le hQ)
      exact_mod_cast giantSampling_residue_card_le r M
    _ = _ := by ring

end ArtinMatthews
