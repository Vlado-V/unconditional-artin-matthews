module

public import ArtinMatthews.GiantSamplingGiantComponent
public import ArtinMatthews.PrimeExtractionWeightBounds
public import ArtinMatthews.HeckePrimeLogSaving


set_option backward.privateInPublic true
@[expose] public section

/-! The marking weights in the giant-factor term of Section 6.1 are the
actual arrays, their products, and fixed linear combinations. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI OAI.SevenEighths
open scoped BigOperators

theorem giantSampling_empty_array (e : PEmpty → ℝ) (x : ℝ) (u : ℕ) :
    literalMarkedArrayWeight e x u = 1 := by
  simp [literalMarkedArrayWeight, divisorWeight]

theorem giantSampling_array_product {J K : Type*} [Fintype J] [Fintype K]
    (e : J → ℝ) (f : K → ℝ) (x : ℝ) (u : ℕ) :
    literalMarkedArrayWeight (Sum.elim e f) x u =
      literalMarkedArrayWeight e x u * literalMarkedArrayWeight f x u := by
  simp only [literalMarkedArrayWeight, divisorWeight, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]

theorem giantCubicSampling_actual_arrays_log_saving
    {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
    (e : ∀ i, J i → ℝ) (he : ∀ i j, 0 < e i j ∧ e i j < 1) (c : I → ℂ)
    (η : HeckeFamily.Character) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) (Φ : ℝ → ℝ)
    (hΦ : ∀ t, ‖Φ t‖ ≤ 1) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound η Φ x (ε / 1024) Cν) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (∑ r ∈ Finset.Icc 1 ⌊x ^ (ε / 64)⌋₊,
        ‖giantCubicSamplingGiantSum η χ
          (fun u => ∑ i, c i * (literalMarkedArrayWeight (e i) x u : ℂ)) Φ ε x r‖) ≤
        x * (Real.log x) ^ (-A) := by
  classical
  let C : ℝ := 1 + ∑ i, ‖c i‖ * (2 / Real.log 2) ^ Fintype.card (J i)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  obtain ⟨C₀, hC₀, hmain⟩ :=
    giantCubicSampling_giantComponent_power_saving η χ hε hεq Φ hΦ hs hsource
  have hbounds := eventually_all.mpr fun i =>
    literalMarkedArrayWeight_bound_eventually (e i) (fun j => (he i j).1)
  have hinvariance := eventually_all.mpr fun i =>
    giantSampling_literalArray_giant_invariant_eventually (e i) (fun j => (he i j).2)
      (hεq.trans (by norm_num))
  have hdecay := heckePrime_uniform_power_log_saving (C₀ * C) (1 - ε / 128) 1 A
    (mul_pos hC₀ hC).le (by linarith) zero_lt_one
  filter_upwards [hmain, hbounds, hinvariance, hdecay] with x hx hb hi hd
  let H (u : ℕ) : ℂ := ∑ i, c i * (literalMarkedArrayWeight (e i) x u : ℂ)
  have hH (u : ℕ) : ‖H u‖ ≤ C := by
    calc
      _ ≤ ∑ i, ‖c i * (literalMarkedArrayWeight (e i) x u : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * (2 / Real.log 2) ^ Fintype.card (J i) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (literalMarkedArrayWeight_nonneg (e i) x u)]
        exact mul_le_mul_of_nonneg_left (hb i u) (norm_nonneg _)
      _ ≤ C := by dsimp only [C]; linarith
  have hInv (ℓ : ℕ) (hℓ : ℓ ∈ giantPrimeWindow x ε) (u : ℕ) :
      H (ℓ * u) = H u := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hi i ℓ hℓ u]
  calc
    _ ≤ C₀ * C * x ^ (1 - ε / 128) := hx H C hC (fun u _ => hH u) hInv
    _ ≤ _ := hd x (by rw [Real.rpow_one])

end ArtinMatthews
