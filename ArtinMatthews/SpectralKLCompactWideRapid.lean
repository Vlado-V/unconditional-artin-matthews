module

public import ArtinMatthews.SpectralKLCompactRapid


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

/-- The doubled K order requires a wider strip than the inverse KL shift. -/
theorem spectralKLCompactOrderTransform_wide_bound (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d t : ℝ, |d| ≤ 3/2 →
      Real.exp (Real.pi*|t|/2) *
        ‖spectralKLCompactOrderTransform f ((d : ℂ)+(t : ℂ)*Complex.I)‖ ≤ C*(1+t^2)^3 := by
  obtain ⟨a,ha,hs⟩ := spectral_compact_positive_lower_bound f hc hp
  obtain ⟨D,hD,hK⟩ := schlafliBesselK_closed_strip_polynomial_bound 3 (3/2) a
    (by norm_num) (by norm_num) ha
  let M := ∫ x : ℝ, ‖spectralKLPhysicalCompactDiv f x‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨D*8/a^3*M,by positivity,?_⟩
  intro d t hd
  let u := 1+t^2
  let E := Real.exp (Real.pi*|t|/2)
  let ν : ℂ := (d : ℂ)+(t : ℂ)*Complex.I
  let B := D*8/a^3*u^3
  have htu : 1+|t| ≤ 2*u := by dsimp [u]; nlinarith [sq_abs t,sq_nonneg (|t|-1)]
  have hpoly : (1+|t|)^3 ≤ 8*u^3 := by
    exact (pow_le_pow_left₀ (by positivity) htu 3).trans_eq (by ring)
  have hdI := spectralKLPhysicalCompactDiv_integrable f hf hc hp
  have hi := spectralKLCompactOrderIntegrand_integrable f hf hc hp ν
  have hb (x : ℝ) : E * ‖spectralKLCompactOrderIntegrand f ν x‖ ≤
      B * ‖spectralKLPhysicalCompactDiv f x‖ := by
    by_cases hfx : f x = 0
    · simp [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,hfx]
    · have hax := hs x (subset_tsupport f hfx)
      have hk : E * ‖schlafliBesselK ν x‖ ≤ B := by
        calc
          _ ≤ D*(1+|t|)^3/x^3 := hK d t x hd hax
          _ ≤ D*(8*u^3)/a^3 :=
            div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpoly hD.le)
              (by positivity) (pow_le_pow_left₀ ha.le hax _)
          _ = _ := by dsimp [B]; ring
      dsimp only [spectralKLCompactOrderIntegrand]
      rw [norm_mul,← mul_assoc]
      exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  calc
    _ ≤ E * ∫ x : ℝ, ‖spectralKLCompactOrderIntegrand f ν x‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_nonneg _)
    _ = ∫ x : ℝ, E * ‖spectralKLCompactOrderIntegrand f ν x‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ x : ℝ, B * ‖spectralKLPhysicalCompactDiv f x‖ :=
      integral_mono_ae (hi.norm.const_mul E) (hdI.norm.const_mul B) (ae_of_all _ hb)
    _ = _ := by rw [integral_const_mul]; dsimp [B,M,u]; ring

theorem spectralKLCompactOrderTransform_wide_rapid (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d t : ℝ, |d| ≤ 3/2 →
      (1+t^2)^N * Real.exp (Real.pi*|t|/2) *
        ‖spectralKLCompactOrderTransform f ((d : ℂ)+(t : ℂ)*Complex.I)‖ ≤ C := by
  obtain ⟨C,hC,hbase⟩ := spectralKLCompactOrderTransform_wide_bound f hf.continuous hc hp
  obtain ⟨hg,hgc,hgp⟩ := spectralKLIteratedOperator_properties f hf hc hp (N+3)
  obtain ⟨D,hD,hiter⟩ := spectralKLCompactOrderTransform_wide_bound
    (spectralKLIteratedOperator f (N+3)) hg.continuous hgc hgp
  refine ⟨C*5^(N+3)+D*2^(N+3),by positivity,?_⟩
  intro d t hd
  let u := 1+t^2
  let E := Real.exp (Real.pi*|t|/2)
  let ν : ℂ := (d : ℂ)+(t : ℂ)*Complex.I
  let V := ‖spectralKLCompactOrderTransform f ν‖
  have hu : 0 < u := by dsimp [u]; positivity
  change u^N*E*V ≤ _
  by_cases ht : 4 ≤ t^2
  · have hd2 : d^2 ≤ (3/2 : ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d) (by norm_num)).mpr hd
    have hreal : u/2 ≤ (1-ν^2).re := by
      norm_num [u,ν,pow_two,Complex.mul_re,Complex.mul_im]
      nlinarith
    have hn : u/2 ≤ ‖1-ν^2‖ := hreal.trans (Complex.re_le_norm _)
    have hpow : (u/2)^(N+3)*V ≤ ‖spectralKLCompactOrderTransform
        (spectralKLIteratedOperator f (N+3)) ν‖ := by
      rw [spectralKLCompactOrderTransform_iterated f hf hc hp,norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn _) (norm_nonneg _)
    have hb : E*((u/2)^(N+3)*V) ≤ D*u^3 :=
      (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)).trans (hiter d t hd)
    have he : E*((u/2)^(N+3)*V) = (u^3/2^(N+3))*(u^N*E*V) := by
      rw [div_pow,pow_add u N 3]
      ring
    rw [he] at hb
    have hs : (u^3/2^(N+3))*(D*2^(N+3)) = D*u^3 := by field_simp <;> ring
    rw [← hs] at hb
    exact (le_of_mul_le_mul_left hb (by positivity)).trans (le_add_of_nonneg_left (by positivity))
  · have h5 : u ≤ 5 := by dsimp [u]; linarith
    calc
      _ = u^N*(E*V) := by ring
      _ ≤ u^N*(C*u^3) := mul_le_mul_of_nonneg_left (hbase d t hd) (by positivity)
      _ = C*u^(N+3) := by rw [pow_add]; ring
      _ ≤ C*5^(N+3) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu.le h5 _) hC
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

end
end ArtinMatthews

