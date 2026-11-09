module

public import ArtinMatthews.SpectralGamma0FiniteGreenPlane
public import ArtinMatthews.SpectralGamma0GreenPlaneBound
public import ArtinMatthews.SpectralFiniteEvaluationDual


set_option backward.privateInPublic true
@[expose] public section

/-! Cardinality-free local spectral bounds derived from actual Green smoothing. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0FiniteGreenPlane_evaluation_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Gamma0AllHeightSpectralIndex N))
      (c : Gamma0AllHeightSpectralIndex N → ℝ) (p : ℝ × ℝ), p ∈ K →
      ‖gamma0FiniteGreenPlane N r Y hY s c p‖ ≤ C*‖gamma0FiniteMassCombination N s c‖ := by
  obtain ⟨C,hC,hb⟩ := gamma0Green_plane_compact_bound N r Y hY hK hKΩ
  exact ⟨C,hC,fun s c p hp => hb _ _ (gamma0FiniteGreenPlane_smooth N r Y hY s c)
    (gamma0FiniteGreenPlane_mass_ae N r Y hY s c) p hp⟩

theorem gamma0FullCuspidalPlaneRepresentative_green_weighted_sum_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Gamma0AllHeightSpectralIndex N)) (p : ℝ × ℝ), p ∈ K →
      (∑ i ∈ s, i.1.re^2*‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2) ≤ C^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FiniteGreenPlane_evaluation_bound N r Y hY hK hKΩ
  refine ⟨2*C,by positivity,?_⟩
  intro s p hp
  let z := fun i : Gamma0AllHeightSpectralIndex N =>
    i.1.re • gamma0FullCuspidalPlaneRepresentative N r Y hY i p
  have hdual : ∀ c : Gamma0AllHeightSpectralIndex N → ℝ,
      ‖∑ i ∈ s, c i • z i‖^2 ≤ C^2*(∑ i ∈ s, (c i)^2) := by
    intro c
    have he : (∑ i ∈ s, c i • z i) = gamma0FiniteGreenPlane N r Y hY s c p := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [z]
      rw [smul_smul,mul_comm]
    rw [he]
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mpr (hb s c p hp)
    rwa [mul_pow,gamma0FiniteMassCombination_norm_sq] at hs
  have he := finite_complex_evaluation_sq_le_of_real_sum_bound s z C hdual
  simp only [z,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at he
  exact he.trans (by nlinarith [sq_nonneg C])

theorem gamma0FullCuspidalPlaneRepresentative_spectral_window_bound
    (N : ℕ) [NeZero N] (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (p : ℝ × ℝ), p ∈ K →
      (∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
        ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2) ≤ (C*(1+R))^2 := by
  obtain ⟨C,hC,hb⟩ := gamma0FullCuspidalPlaneRepresentative_green_weighted_sum_bound N r Y hY hK hKΩ
  refine ⟨C,hC,?_⟩
  intro R p hp
  have hpoint (i : Gamma0AllHeightSpectralIndex N)
      (hi : i ∈ gamma0AllHeightGradientSpectralCutoff N R) :
      ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2 ≤
        (1+R)^2*(i.1.re^2*‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2) := by
    have hμ := gamma0AllHeightSpectralValue_pos N i
    have hval := (mem_gamma0AllHeightGradientSpectralCutoff N R i).mp hi
    change i.1.re⁻¹-1 ≤ R at hval
    have hinv : i.1.re⁻¹ ≤ 1+R := by linarith
    have hprod := mul_le_mul_of_nonneg_right hinv hμ.le
    rw [inv_mul_cancel₀ hμ.ne'] at hprod
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hprod 2
    rw [one_pow,mul_pow] at hs
    have ht := mul_le_mul_of_nonneg_right hs
      (sq_nonneg ‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖)
    simpa only [one_mul,mul_assoc] using ht
  calc
    _ ≤ ∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
        (1+R)^2*(i.1.re^2*‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2) :=
      Finset.sum_le_sum hpoint
    _ = (1+R)^2*∑ i ∈ gamma0AllHeightGradientSpectralCutoff N R,
        i.1.re^2*‖gamma0FullCuspidalPlaneRepresentative N r Y hY i p‖^2 := by rw [Finset.mul_sum]
    _ ≤ (1+R)^2*C^2 := mul_le_mul_of_nonneg_left (hb _ p hp) (sq_nonneg _)
    _ = (C*(1+R))^2 := by ring

end ArtinMatthews
