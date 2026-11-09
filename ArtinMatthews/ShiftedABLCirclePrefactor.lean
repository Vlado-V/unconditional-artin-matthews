module

public import ArtinMatthews.CircleNormalizerSmoothBounds
public import ArtinMatthews.CubicThetaDualZeroNormalized


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nebentypus and totient normalization in the source Mellin
identity, with the modulus quotient and its cancellation kept explicit. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABL_circle_prefactor_bound (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F r L m3 m4 : ℕ),
      0 < F → 0 < r → F.Coprime r → 4*(F*r) ≤ L →
      let Λ := circleNormalizer (circleModuli F r L) (circleSmoothWeight L)
      let Q : ℝ := 3*(L : ℝ)
      ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
        ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))‖ ≤
          C*(r : ℝ)^η/((L : ℝ)^(2-η)*Q) := by
  obtain ⟨c,hc,hlower⟩ := circleSmoothNormalizer_lower η hη hη1
  refine ⟨c⁻¹,inv_pos.mpr hc,?_⟩
  intro F r L m3 m4 hF hr hFr hL Λ Q
  have hFp : (0 : ℝ) < F := by exact_mod_cast hF
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hLp : (0 : ℝ) < L := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4*(F*r)) hL)
  have hΛ : 0 < Λ := circleSmoothNormalizer_positive hF hr hFr hL
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hb := hlower F r L hF hr hFr hL
  change c*(L : ℝ)^(2-η)/((F : ℝ)*(r : ℝ)^η) ≤ Λ at hb
  have hden : c*((L : ℝ)^(2-η)*Q) ≤ (Λ*(F : ℝ)*Q)*(r : ℝ)^η := by
    have ht := (div_le_iff₀ (by positivity : 0 < (F : ℝ)*(r : ℝ)^η)).mp hb
    convert mul_le_mul_of_nonneg_right ht hQ.le using 1 <;> ring
  rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos hΛ,abs_of_pos hQ]
  calc
    _ ≤ 1/(Λ*(F : ℝ)*Q) := div_le_div_of_nonneg_right
      (cubicThetaNebentypus_norm_le_one _) (by positivity)
    _ ≤ c⁻¹*(r : ℝ)^η/((L : ℝ)^(2-η)*Q) := by
      apply (div_le_div_iff₀ (by positivity : 0 < Λ*(F : ℝ)*Q)
        (by positivity : 0 < (L : ℝ)^(2-η)*Q)).2
      simp only [one_mul]
      change (L : ℝ)^(2-η)*Q ≤ (c⁻¹*(r : ℝ)^η)*(Λ*(F : ℝ)*Q)
      calc
        _ ≤ ((Λ*(F : ℝ)*Q)*(r : ℝ)^η)/c :=
          (le_div_iff₀ hc).mpr (by simpa only [mul_comm c] using hden)
        _ = _ := by ring


/-- The same normalization expressed at the literal source scale `Q=3L`. -/
theorem shiftedABL_circle_prefactor_Q_bound (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F r L m3 m4 : ℕ),
      0 < F → 0 < r → F.Coprime r → 4*(F*r) ≤ L →
      let Λ := circleNormalizer (circleModuli F r L) (circleSmoothWeight L)
      let Q : ℝ := 3*(L : ℝ)
      ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
        ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))‖ ≤
          C*(Q^η*(r : ℝ)^η)/Q^3 := by
  obtain ⟨C,hC,hbound⟩ := shiftedABL_circle_prefactor_bound η hη hη1
  refine ⟨9*C,by positivity,?_⟩
  intro F r L m3 m4 hF hr hFr hL Λ Q
  have hLp : (0 : ℝ) < L := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4*(F*r)) hL)
  have hQp : 0 < Q := by dsimp [Q]; positivity
  have hLQ : (L : ℝ) ≤ Q := by dsimp [Q]; linarith
  have hpow : (L : ℝ)^(2-η) = (L : ℝ)^2/(L : ℝ)^η := by
    rw [Real.rpow_sub hLp,Real.rpow_two]
  calc
    _ ≤ C*(r : ℝ)^η/((L : ℝ)^(2-η)*Q) := hbound F r L m3 m4 hF hr hFr hL
    _ = (9*C)*((L : ℝ)^η*(r : ℝ)^η)/Q^3 := by
      rw [hpow]
      dsimp [Q]
      field_simp [hLp.ne', (Real.rpow_pos_of_pos hLp η).ne']
      <;> ring
    _ ≤ (9*C)*(Q^η*(r : ℝ)^η)/Q^3 := by
      gcongr

/-- The external `F sqrt(r)` from the actual spectral block leaves this
literal normalized factor. -/
theorem shiftedABL_circle_prefactor_mul_bound (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F r L m3 m4 : ℕ),
      0 < F → 0 < r → F.Coprime r → 4*(F*r) ≤ L →
      let Λ := circleNormalizer (circleModuli F r L) (circleSmoothWeight L)
      let Q : ℝ := 3*(L : ℝ)
      ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
        ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))‖*((F : ℝ)*Real.sqrt r) ≤
          C*((F : ℝ)*Real.sqrt r)*(r : ℝ)^η/((L : ℝ)^(2-η)*Q) := by
  obtain ⟨C,hC,hbound⟩ := shiftedABL_circle_prefactor_bound η hη hη1
  refine ⟨C,hC,?_⟩
  intro F r L m3 m4 hF hr hFr hL Λ Q
  have h := mul_le_mul_of_nonneg_right (hbound F r L m3 m4 hF hr hFr hL)
    (show 0 ≤ (F : ℝ)*Real.sqrt r by positivity)
  convert h using 1 <;> ring

end ArtinMatthews
