module

public import ArtinMatthews.SpectralTrueWidthOrbitalKloosterman
public import ArtinMatthews.SpectralHyperbolicBochnerCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit Cartesian coordinates for the genuine Weyl orbital integral. -/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped MatrixGroups InnerProductSpace ContDiff NNReal

namespace ArtinMatthews

theorem upperHalfPlane_integrable_coordinates_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : ℝ × ℝ → E) :
    Integrable (fun z : UpperHalfPlane => G (z.re,z.im)) ↔
      IntegrableOn (fun p => (p.2^2)⁻¹ • G p) {p : ℝ × ℝ | 0 < p.2} := by
  have hcoe : MeasurePreserving UpperHalfPlane.coe
      (volume.comap UpperHalfPlane.coe) (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe,UpperHalfPlane.measurableEmbedding_coe.map_comap volume⟩
  let S : Set (ℝ × ℝ) := {p | 0 < p.2}
  have hprod : MeasurePreserving Complex.measurableEquivRealProd
      (volume.restrict (Complex.measurableEquivRealProd ⁻¹' S)) (volume.restrict S) := by
    refine ⟨Complex.measurableEquivRealProd.measurable,?_⟩
    rw [← Complex.measurableEquivRealProd.restrict_map,Complex.volume_preserving_equiv_real_prod.map_eq]
  rw [UpperHalfPlane.volume_def,integrable_withDensity_iff_integrable_smul (by fun_prop)]
  have he : (fun z : UpperHalfPlane =>
      ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0)^2) • G (z.re,z.im)) =
      (fun z : UpperHalfPlane => (z.im^2)⁻¹ • G (z.re,z.im)) := by
    funext z
    rw [NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
      NNReal.coe_mk,one_div,inv_pow]
  rw [he]
  change Integrable ((fun z : ℂ => (z.im^2)⁻¹ • G (z.re,z.im)) ∘ UpperHalfPlane.coe)
    (volume.comap UpperHalfPlane.coe) ↔ _
  rw [hcoe.integrable_comp_emb UpperHalfPlane.measurableEmbedding_coe]
  convert hprod.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding
    (g := fun p => (p.2^2)⁻¹ • G p) using 1
  · rw [UpperHalfPlane.range_coe]
    rfl
  · rfl

theorem realWeylMatrix_re (c : ℝ) (hc : c ≠ 0) (z : UpperHalfPlane) :
    (realWeylMatrix c hc • z).re = -z.re / (c^2*Complex.normSq (z : ℂ)) := by
  have h := congrArg Complex.re (realWeylMatrix_coe_smul c hc z)
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.inv_re] at h
  change (realWeylMatrix c hc • z).re = -(c^2)⁻¹ * (z.re / Complex.normSq (z : ℂ)) at h
  rw [h]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

theorem atkinPhase_conj (x : ℝ) : star (atkinPhase x) = atkinPhase (-x) := by
  unfold atkinPhase
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
  ring

def weylPlanarPhase (N : ℕ) (m n : ℤ) (c x y : ℝ) : ℝ :=
  -((m : ℝ)*x + (n : ℝ)*x/(c^2*(x^2+y^2)))/(N : ℝ)

def weylPlanarAmplitude (ρ η : ℝ → ℝ) (c x y : ℝ) : ℝ :=
  ρ y * η (y/(c^2*(x^2+y^2)))

def weylPlanarIntegrand (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (p : ℝ × ℝ) : ℂ :=
  (weylPlanarAmplitude ρ η c p.1 p.2 : ℂ) * atkinPhase (weylPlanarPhase N m n c p.1 p.2)

def weylPlanarDensity (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (p : ℝ × ℝ) : ℂ := (p.2^2)⁻¹ • weylPlanarIntegrand N m n ρ η c p

theorem cuspWeylOrbitalIntegrand_coordinates (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0) (z : UpperHalfPlane) :
    cuspWeylOrbitalIntegrand N m n ρ η c hc z =
      weylPlanarIntegrand N m n ρ η c (z.re,z.im) := by
  have hphase : cuspFourierPhase (N : ℝ) m z.re *
      star (cuspFourierPhase (N : ℝ) n (realWeylMatrix c hc • z).re) =
      atkinPhase (weylPlanarPhase N m n c z.re z.im) := by
    rw [realWeylMatrix_re,cuspFourierPhase_as_atkinPhase,
      cuspFourierPhase_as_atkinPhase,atkinPhase_conj,← atkinPhase_add]
    congr 1
    rw [Complex.normSq_apply]
    unfold weylPlanarPhase
    change -↑m*z.re/↑N + -(-↑n*(-z.re/(c^2*(z.re*z.re+z.im*z.im)))/↑N) = _
    ring
  have hs : star (ρ z.im : ℂ) = (ρ z.im : ℂ) := by simp
  unfold cuspWeylOrbitalIntegrand cuspFourierWave
  rw [RCLike.inner_apply]
  simp only [map_mul,starRingEnd_apply,star_star,hs]
  unfold weylPlanarIntegrand weylPlanarAmplitude
  rw [← hphase,realWeylMatrix_im,Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  push_cast
  ring

theorem cuspWeylOrbitalKernel_coordinates (N : ℕ) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    cuspWeylOrbitalKernel N m n ρ η c hc =
      ∫ p in {p : ℝ × ℝ | 0 < p.2}, weylPlanarDensity N m n ρ η c p := by
  unfold cuspWeylOrbitalKernel weylPlanarDensity
  simp_rw [cuspWeylOrbitalIntegrand_coordinates]
  exact upperHalfPlane_integral_coordinates_smul _

theorem weylPlanarDensity_integrable (N : ℕ) [NeZero N] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (c : ℤ) (hc : c ≠ 0) :
    IntegrableOn (weylPlanarDensity N m n ρ η c) {p : ℝ × ℝ | 0 < p.2} := by
  apply (upperHalfPlane_integrable_coordinates_smul _).mp
  simp_rw [← cuspWeylOrbitalIntegrand_coordinates N m n ρ η (c : ℝ) (by exact_mod_cast hc)]
  exact cuspWeylOrbitalIntegrand_integrable N m n ρ η hρ hη hcρ hcη hpρ hpη c hc

end ArtinMatthews
