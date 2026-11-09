module

public import ArtinMatthews.SpectralCuspProfileNorm


set_option backward.privateInPublic true
@[expose] public section

/-! An annular height profile has an explicit native Poincare norm.
The estimate is uniform in its Fourier index, with fixed level and cusp. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem cuspFourierHeightPairing_annulus_le (ρ : ℝ → ℝ) (hρ : Continuous ρ)
    {A M : ℝ} (hA : 0 < A) (_hM : 0 ≤ M)
    (hs : tsupport ρ ⊆ Icc A (4*A)) (hb : ∀ y, ‖ρ y‖ ≤ M) :
    cuspFourierHeightPairing ρ ρ ≤ 3*M^2/A := by
  let S := Icc A (4*A)
  have hS : S ⊆ Ioi (0 : ℝ) := fun _ hy => hA.trans_le hy.1
  have he : cuspFourierHeightPairing ρ ρ = ∫ y in S, (ρ y)^2/y^2 := by
    unfold cuspFourierHeightPairing
    simp_rw [← pow_two]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hS
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy.2 (hs h)),zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div]
  have hI : IntegrableOn (fun y => (ρ y)^2/y^2) S :=
    ((hρ.pow 2).continuousOn.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (hS hy).ne')).integrableOn_Icc
  rw [he]
  calc
    _ ≤ ∫ _y in S, M^2/A^2 := by
      apply setIntegral_mono_on hI (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc
      intro y hy
      have hsq : (ρ y)^2 ≤ M^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (ρ y)) (hb y) 2
      have hyA : A^2 ≤ y^2 := pow_le_pow_left₀ hA.le hy.1 2
      calc
        _ ≤ M^2/y^2 := div_le_div_of_nonneg_right hsq (sq_nonneg _)
        _ ≤ M^2/A^2 := div_le_div_of_nonneg_left (sq_nonneg M) (sq_pos_of_pos hA) hyA
    _ = _ := by
      dsimp only [S]
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show A ≤ 4*A by linarith),
        intervalIntegral.integral_const,smul_eq_mul]
      field_simp [hA.ne']
      ring

def gamma0PrimitiveAnnularNormConstant (N : ℕ) [NeZero N] (a : SL(2, ℤ)) : ℝ :=
  Real.sqrt (3*gamma0PrimitiveProfileNormConstant N a)

theorem gamma0PrimitiveFourierPoincareTest_annulus_norm_le (N : ℕ) [NeZero N]
    (a : SL(2, ℤ)) (n : ℤ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    {A M : ℝ} (hA : 0 < A) (hM : 0 ≤ M)
    (hs : tsupport ρ ⊆ Icc A (4*A)) (hb : ∀ y, ‖ρ y‖ ≤ M) :
    ‖gamma0PrimitiveFourierPoincareTest N a n ρ hρ hcρ hpρ‖ ≤
      gamma0PrimitiveAnnularNormConstant N a*M*(1+2/A) := by
  let K := gamma0PrimitiveProfileNormConstant N a
  have hK : 0 ≤ K := by dsimp [K,gamma0PrimitiveProfileNormConstant]; positivity
  have hfac : 0 ≤ 1+2/A := by positivity
  have hsq := gamma0PrimitiveFourierPoincareTest_orbit_normsq_le N a n ρ hρ hcρ hpρ hA
    (fun y hy => (hs hy).1)
  have hmass := cuspFourierHeightPairing_annulus_le ρ hρ.continuous hA hM hs hb
  have hsmall : (1+2/A)/A ≤ (1+2/A)^2 := by
    rw [div_eq_mul_inv,pow_two]
    apply mul_le_mul_of_nonneg_left _ hfac
    have hi : 0 < A⁻¹ := inv_pos.mpr hA
    simp only [div_eq_mul_inv]
    linarith
  have hmain : ‖gamma0PrimitiveFourierPoincareTest N a n ρ hρ hcρ hpρ‖^2 ≤
      (gamma0PrimitiveAnnularNormConstant N a*M*(1+2/A))^2 := by
    calc
      _ ≤ K*(1+2/A)*(3*M^2/A) :=
        hsq.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hK hfac))
      _ = (3*K*M^2)*((1+2/A)/A) := by ring
      _ ≤ (3*K*M^2)*(1+2/A)^2 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by
        rw [mul_pow,mul_pow,gamma0PrimitiveAnnularNormConstant,Real.sq_sqrt (by positivity : 0 ≤ 3*K)]
  exact (sq_le_sq₀ (norm_nonneg _) (by unfold gamma0PrimitiveAnnularNormConstant; positivity)).mp hmain

end ArtinMatthews
