module

public import ArtinMatthews.SpectralWeylPhysicalBilinearGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! Exact fixed-interval substitution for the true two-height orbital
kernel.  Folding at the square-root boundary removes its singularity,
without changing the positive-modulus or frequency normalization. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralWeylFoldHeight (B u : ℝ) : ℝ := B*(1-u^2)

theorem spectralWeylFoldHeight_image {B : ℝ} (hB : 0 < B) :
    spectralWeylFoldHeight B '' Ioo (0 : ℝ) 1 = Ioo 0 B := by
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hlt : u^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
    exact ⟨mul_pos hB (sub_pos.mpr hlt),by
      unfold spectralWeylFoldHeight
      nlinarith [mul_pos hB (sq_pos_of_pos hu.1)]⟩
  · intro hz
    have hp : 0 < 1-z/B := sub_pos.mpr ((div_lt_one hB).mpr hz.2)
    have hlt : 1-z/B < 1 := by linarith [div_pos hz.1 hB]
    refine ⟨Real.sqrt (1-z/B),⟨Real.sqrt_pos.mpr hp,(Real.sqrt_lt' one_pos).mpr (by simpa using hlt)⟩,?_⟩
    unfold spectralWeylFoldHeight
    rw [Real.sq_sqrt hp.le]
    field_simp [hB.ne']
    ring_nf

theorem spectralWeylFoldHeight_injOn {B : ℝ} (hB : 0 < B) :
    InjOn (spectralWeylFoldHeight B) (Ioo (0 : ℝ) 1) := by
  intro u hu v hv h
  unfold spectralWeylFoldHeight at h
  have he := mul_left_cancel₀ hB.ne' h
  have hu0 : 0 < u := hu.1
  have hv0 : 0 < v := hv.1
  nlinarith

theorem spectralWeylFoldHeight_hasDerivAt (B u : ℝ) :
    HasDerivAt (spectralWeylFoldHeight B) (-(2*B*u)) u := by
  have hd := ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)).const_mul B
  convert! hd using 1
  norm_num
  ring_nf

theorem spectralWeylFoldHeight_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (F : ℝ → E) :
    (∫ z in Ioo (0 : ℝ) B, F z) =
      ∫ u in Ioo (0 : ℝ) 1, (2*B*u : ℝ) • F (spectralWeylFoldHeight B u) := by
  conv_lhs => rw [← spectralWeylFoldHeight_image hB]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u _ => (spectralWeylFoldHeight_hasDerivAt B u).hasDerivWithinAt)
    (spectralWeylFoldHeight_injOn hB)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [abs_neg,abs_of_pos (mul_pos (mul_pos two_pos hB) hu.1)]

theorem spectralWeylFoldHeight_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ} (hB : 0 < B) (F : ℝ → E) :
    IntegrableOn F (Ioo (0 : ℝ) B) ↔
      IntegrableOn (fun u => (2*B*u : ℝ) • F (spectralWeylFoldHeight B u)) (Ioo (0 : ℝ) 1) := by
  conv_lhs => rw [← spectralWeylFoldHeight_image hB]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u _ => (spectralWeylFoldHeight_hasDerivAt B u).hasDerivWithinAt)
    (spectralWeylFoldHeight_injOn hB)]
  apply integrableOn_congr_fun
  · intro u hu
    dsimp only
    rw [abs_neg,abs_of_pos (mul_pos (mul_pos two_pos hB) hu.1)]
  · exact measurableSet_Ioo

def spectralWeylFoldDensity (s t : ℝ) (f g : ℝ → ℂ) (X : ℝ) (q : ℝ × ℝ) : ℂ :=
  let z := spectralWeylFoldHeight (X^2/(4*q.1)) q.2
  ((4/(X*(1-q.2^2))*Real.cos ((s*q.1+t*z)*q.2/Real.sqrt (1-q.2^2)) : ℝ) : ℂ)*
    f z*star (g q.1)

theorem spectralWeylDimensionlessKernel_zero_of_cut {X x z : ℝ} (hX : 0 < X) (hx : 0 < x)
    (hz : X^2/(4*x) ≤ z) (s t : ℝ) : spectralWeylDimensionlessKernel s t X x z = 0 := by
  have hA : X^2 ≤ 4*x*z := by
    have h := (div_le_iff₀ (by positivity : 0 < 4*x)).mp hz
    nlinarith
  have hh : X ≤ Real.sqrt (4*x*z) := by
    simpa only [Real.sqrt_sq hX.le] using Real.sqrt_le_sqrt hA
  simp only [spectralWeylDimensionlessKernel,spectralWeylRadialKernel,ite_eq_right (not_lt.mpr hh)]

theorem spectralWeylDimensionlessKernel_fold {X x u : ℝ} (hX : 0 < X) (hx : 0 < x)
    (hu : u ∈ Ioo (0 : ℝ) 1) (s t : ℝ) :
    let z := spectralWeylFoldHeight (X^2/(4*x)) u
    spectralWeylDimensionlessKernel s t X x z =
      2*Real.cos ((s*x+t*z)*u/Real.sqrt (1-u^2))/(X*u) := by
  dsimp only
  let z := spectralWeylFoldHeight (X^2/(4*x)) u
  change spectralWeylDimensionlessKernel s t X x z = _
  have hA : 4*x*z = X^2*(1-u^2) := by
    dsimp [z,spectralWeylFoldHeight]
    field_simp [hx.ne']
  have hcut : Real.sqrt (4*x*z) < X := by
    apply (Real.sqrt_lt' hX).mpr
    rw [hA]
    nlinarith [mul_pos (sq_pos_of_pos hX) (sq_pos_of_pos hu.1)]
  have hroot : Real.sqrt (X^2-4*x*z) = X*u := by
    rw [hA,show X^2-X^2*(1-u^2) = X^2*u^2 by ring,
      Real.sqrt_mul (sq_nonneg X),Real.sqrt_sq hX.le,Real.sqrt_sq hu.1.le]
  have hroot2 : 2*Real.sqrt (x*z) = X*Real.sqrt (1-u^2) := by
    have h := congrArg Real.sqrt hA
    rw [show 4*x*z = 4*(x*z) by ring,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      Real.sqrt_mul (sq_nonneg X),Real.sqrt_sq hX.le] at h
    norm_num at h
    exact h
  unfold spectralWeylDimensionlessKernel spectralWeylRadialKernel
  rw [ite_eq_left hcut,hroot,hroot2]
  have hw : 0 < 1-u^2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
  have hp : (s*x+t*z)/(X*Real.sqrt (1-u^2))*(X*u) = (s*x+t*z)*u/Real.sqrt (1-u^2) := by
    field_simp [hX.ne',(Real.sqrt_pos.mpr hw).ne']
  rw [hp]

theorem spectralWeylFoldDensity_jacobian {X x u : ℝ} (hX : 0 < X) (hx : 0 < x)
    (hu : u ∈ Ioo (0 : ℝ) 1) (s t : ℝ) (f g : ℝ → ℂ) :
    let B := X^2/(4*x)
    let z := spectralWeylFoldHeight B u
    (2*B*u : ℝ) • ((z⁻¹ : ℂ)*spectralWeylPhysicalIntegrand s t f g ((x,z),X)) =
      spectralWeylFoldDensity s t f g X (x,u) := by
  dsimp only
  let B := X^2/(4*x)
  let z := spectralWeylFoldHeight B u
  let c := Real.cos ((s*x+t*z)*u/Real.sqrt (1-u^2))
  have hw : 0 < 1-u^2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
  have hB : 0 < B := by dsimp [B]; positivity
  have he : (2*B*u)*z⁻¹*(2*c/(X*u)) = 4/(X*(1-u^2))*c := by
    dsimp only [z,spectralWeylFoldHeight]
    field_simp [hB.ne',hX.ne',hu.1.ne',hw.ne']
    ring_nf
  calc
    _ = (((2*B*u)*z⁻¹*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*f z*star (g x) := by
      change (2*B*u : ℝ) • ((z⁻¹ : ℂ)*
        ((spectralWeylDimensionlessKernel s t X x z : ℂ)*f z*star (g x))) = _
      rw [Complex.real_smul]
      push_cast
      ring_nf
    _ = _ := by
      rw [spectralWeylDimensionlessKernel_fold hX hx hu s t]
      change ((↑((2*B*u)*z⁻¹*(2*c/(X*u))) : ℂ))*f z*star (g x) = _
      rw [he]
      rfl

end ArtinMatthews
