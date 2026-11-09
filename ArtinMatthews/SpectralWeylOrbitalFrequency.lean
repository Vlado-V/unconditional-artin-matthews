module

public import ArtinMatthews.SpectralWeylPhysicalHeightDilation
public import ArtinMatthews.SpectralWeylFrequencyScaling


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of the literal orbital kernel with the checked
unregularized physical pairing, at its exact frequency-dilated modulus.
The prefactor sqrt(a*b)/C^2 and both signed frequencies remain literal. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralWeyl_scaled_cut {a b C y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : 0 < C) (hy : 0 < y) :
    (Real.sqrt (a*b)*(2/C))^2/(4*(a*y)) = b/(C^2*y) := by
  rw [mul_pow,Real.sq_sqrt (mul_pos ha hb).le]
  field_simp [ha.ne',hC.ne',hy.ne']
  ring_nf

theorem cuspWeylOrbitalKernel_frequency_physical (N : ℕ) [NeZero N] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hη : Continuous η) (hcη : HasCompactSupport η) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (hI : IntegrableOn (weylPlanarDensity N m n ρ η C) {p : ℝ × ℝ | 0 < p.2}) :
    cuspWeylOrbitalKernel N m n ρ η C hC.ne' =
      ((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)*
        spectralWeylPhysicalBilinear (cuspFourierFrequency (N : ℝ) m/a) (cuspFourierFrequency (N : ℝ) n/b)
          (spectralKLHeightPhysicalTest b η) (spectralKLHeightPhysicalTest a ρ) (Real.sqrt (a*b)*(2/C)) := by
  let X := Real.sqrt (a*b)*(2/C)
  let s := cuspFourierFrequency (N : ℝ) m/a
  let t := cuspFourierFrequency (N : ℝ) n/b
  let P : ℂ := ((Real.sqrt (a*b)/C^2 : ℝ) : ℂ)
  have hX : 0 < X := mul_pos (Real.sqrt_pos.mpr (mul_pos ha hb)) (div_pos two_pos hC)
  change cuspWeylOrbitalKernel N m n ρ η C hC.ne' =
    P*spectralWeylPhysicalBilinear s t (spectralKLHeightPhysicalTest b η) (spectralKLHeightPhysicalTest a ρ) X
  rw [cuspWeylOrbitalKernel_twoHeight N m n ρ η C hC.ne' hI,
    spectralWeylPhysicalBilinear_height_dilation ha hb hX s t ρ η hρ hcρ hpρ hη hcη hpη,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := hy
  let F : ℝ → ℂ := fun v => (spectralWeylDimensionlessKernel s t X (a*y) (b*v) : ℂ)*
    spectralKLHeightBaseTest η v*spectralKLHeightBaseTest ρ y/(v : ℂ)
  change (∫ v in Ioo (0 : ℝ) (1/(C^2*y)), weylTwoHeightDensity N m n ρ η C y v) =
    P*((∫ v in Ioi (0 : ℝ), F v)/(y : ℂ))
  have hcut : (∫ v in Ioi (0 : ℝ), F v) = ∫ v in Ioo (0 : ℝ) (1/(C^2*y)), F v := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
    intro v hv
    have hvB : 1/(C^2*y) ≤ v := le_of_not_gt (fun hlt => hv.2 ⟨hv.1,hlt⟩)
    have hscaled : X^2/(4*(a*y)) ≤ b*v := by
      change (Real.sqrt (a*b)*(2/C))^2/(4*(a*y)) ≤ b*v
      rw [spectralWeyl_scaled_cut ha hb hC hy0]
      have hh := mul_le_mul_of_nonneg_left hvB hb.le
      simpa only [mul_one_div] using hh
    dsimp only [F]
    rw [spectralWeylDimensionlessKernel_zero_of_cut hX (mul_pos ha hy0) hscaled,
      Complex.ofReal_zero,zero_mul,zero_mul,zero_div]
  rw [hcut,div_eq_mul_inv (∫ v in Ioo (0 : ℝ) (1/(C^2*y)), F v) (y : ℂ),
    ← integral_mul_const,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  dsimp only
  rw [weylTwoHeightDensity_frequency_scaled N m n ρ η ha hb hC hy0 hv]
  unfold F P spectralKLHeightBaseTest
  dsimp only [X,s,t]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hC.ne',Complex.ofReal_ne_zero.mpr hy0.ne',
    Complex.ofReal_ne_zero.mpr hv.1.ne']

end ArtinMatthews
