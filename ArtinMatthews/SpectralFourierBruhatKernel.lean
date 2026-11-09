module

public import ArtinMatthews.SpectralCuspBruhatKernel
public import ArtinMatthews.SpectralFourierParabolicUnfolding


set_option backward.privateInPublic true
@[expose] public section

/-! The exact arithmetic Fourier phase of each nonzero-modulus geometric
kernel.  Shifted compact windows are retained until orbital summation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem realTranslation_coe_smul (x : ℝ) (z : UpperHalfPlane) :
    ((realTranslation x • z : UpperHalfPlane) : ℂ) = z + x := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [realTranslation]

theorem realTranslation_re_smul (x : ℝ) (z : UpperHalfPlane) :
    (realTranslation x • z).re = z.re + x := by
  change (((realTranslation x • z : UpperHalfPlane) : ℂ)).re = _
  rw [realTranslation_coe_smul]
  simp

theorem realTranslation_im_smul (x : ℝ) (z : UpperHalfPlane) :
    (realTranslation x • z).im = z.im := by
  change (((realTranslation x • z : UpperHalfPlane) : ℂ)).im = _
  rw [realTranslation_coe_smul]
  simp

theorem cuspFourierPhase_star (w : ℝ) (n : ℤ) (x : ℝ) :
    star (cuspFourierPhase w n x) = cuspFourierPhase w n (-x) := by
  unfold cuspFourierPhase
  change (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
  ring

theorem cuspFourierPhase_bruhat_factor (N : ℕ) (m n : ℤ) (α β : ℝ) :
    cuspFourierPhase (N : ℝ) m (-β) * star (cuspFourierPhase (N : ℝ) n α) =
      atkinPhase (((m : ℝ) * β + (n : ℝ) * α) / N) := by
  rw [cuspFourierPhase_star,cuspFourierPhase_as_atkinPhase,cuspFourierPhase_as_atkinPhase,
    ← atkinPhase_add]
  congr 1
  ring

def fourierBruhatWindowKernel (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0) (α β : ℝ) : ℂ :=
  ∫ z : UpperHalfPlane,
    (spectralHorizontalPartition (N : ℝ) (z.re - β) *
      spectralHorizontalPartition (N : ℝ) ((realWeylMatrix c hc • z).re + α)) •
        inner ℂ (cuspFourierWave N m ρ z) (cuspFourierWave N n η (realWeylMatrix c hc • z))

theorem compactBruhatWindowKernel_fourier (N : ℕ) [NeZero N]
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (c : ℝ) (hc : c ≠ 0) (α β : ℝ) :
    compactBruhatWindowKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη)
      c hc α β =
      atkinPhase (((m : ℝ) * β + (n : ℝ) * α) / N) *
        fourierBruhatWindowKernel N m n ρ η c hc α β := by
  unfold compactBruhatWindowKernel fourierBruhatWindowKernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← cuspFourierPhase_bruhat_factor]
  simp only [cuspFourierTestSeed_apply,realTranslation_re_smul,realTranslation_im_smul,
    cuspFourierWave,sub_eq_add_neg,cuspFourierPhase_add]
  have hr (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [RCLike.inner_apply,map_mul,starRingEnd_apply,star_mul,star_star,hr,
    Complex.real_smul,Complex.ofReal_mul]
  ring

theorem compactPoincareGeometricKernel_fourier_phase (N : ℕ) [NeZero N]
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (M : SL(2, ℤ)) {c : ℤ} (hc : c ≠ 0) (hM : M 1 0 = c) :
    compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη) M =
      cuspGeometricPhase N m n c M * fourierBruhatWindowKernel N m n ρ η
        (c : ℝ) (by exact_mod_cast hc) ((M 0 0 : ℝ) / c) ((M 1 1 : ℝ) / c) := by
  rw [compactPoincareGeometricKernel_bruhat _ _ M hc hM,compactBruhatWindowKernel_fourier]
  congr 1
  unfold cuspGeometricPhase
  congr 1
  ring

end ArtinMatthews
