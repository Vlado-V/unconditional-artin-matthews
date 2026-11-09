module

public import ArtinMatthews.SpectralPeterssonCutSeedKernel
public import ArtinMatthews.SpectralWeylPlanarCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cut-seed Petersson mass and integrability, including weight two.
Horizontal orthogonality removes every off-diagonal frequency pair. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate

namespace ArtinMatthews

private def cutHorizontal (m n : ℕ+) (x : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => atkinPhase (((n : ℝ)-(m : ℝ))*x)) x

private theorem cutHorizontal_integrable (m n : ℕ+) : Integrable (cutHorizontal m n) := by
  have hc : Continuous (fun x : ℝ => atkinPhase (((n : ℝ)-(m : ℝ))*x)) := by
    unfold atkinPhase
    fun_prop
  exact ((hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

private theorem cutHorizontal_integral (m n : ℕ+) :
    (∫ x, cutHorizontal m n x) = if m = n then 1 else 0 := by
  unfold cutHorizontal
  rw [integral_indicator measurableSet_Ioc]
  have he : (fun x : ℝ => atkinPhase (((n : ℝ)-(m : ℝ))*x)) =
      fun x : ℝ => atkinPhase ((((n : ℤ)-(m : ℤ) : ℤ) : ℝ)*x) := by
    funext x
    push_cast
    rfl
  have hd : ((n : ℤ)-(m : ℤ) = 0) ↔ m = n := by
    constructor
    · intro h
      apply Subtype.ext
      exact (Int.natCast_inj.mp (sub_eq_zero.mp h)).symm
    · rintro rfl
      ring
  rw [he,spectralPeterssonPhase_integral]
  simp only [hd]

theorem spectralPeterssonStripCut_inner_integrable (k : ℕ) (hk : 2 ≤ k)
    (m n : ℕ+) (A : ℝ) :
    Integrable (fun z : UpperHalfPlane => UpperHalfPlane.petersson (k : ℤ)
      (spectralPeterssonStripCutSeed m A) (spectralPeterssonStripCutSeed n A) z) := by
  let V := spectralPeterssonCutPairRadial k m n A
  let G (p : ℝ × ℝ) : ℂ := cutHorizontal m n p.1*(p.2^2*V p.2 : ℝ)
  let S := (univ : Set ℝ) ×ˢ Ioi (0 : ℝ)
  have hS : {p : ℝ × ℝ | 0 < p.2} = S := by ext p; simp [S]
  have hi : IntegrableOn (fun p : ℝ × ℝ => cutHorizontal m n p.1*(V p.2 : ℂ)) S
      (volume.prod volume) := by
    rw [IntegrableOn,← Measure.prod_restrict]
    simpa only [Measure.restrict_univ,V] using! (cutHorizontal_integrable m n).mul_prod
      (spectralPeterssonCutPairRadial_integrable k hk m n A).ofReal
  have he : (fun z : UpperHalfPlane => UpperHalfPlane.petersson (k : ℤ)
      (spectralPeterssonStripCutSeed m A) (spectralPeterssonStripCutSeed n A) z) =
      fun z : UpperHalfPlane => G (z.re,z.im) := by
    funext z
    exact spectralPeterssonStripCut_pair_coordinates k hk m n A z
  rw [he,upperHalfPlane_integrable_coordinates_smul,hS]
  apply hi.congr_fun _ ((MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod measurableSet_Ioi)
  intro p hp
  have hy : p.2 ≠ 0 := (show 0 < p.2 from hp.2).ne'
  dsimp only [G]
  rw [Complex.real_smul]
  push_cast
  field_simp [hy]

theorem spectralPeterssonStripCut_inner (k : ℕ) (hk : 2 ≤ k)
    (m n : ℕ+) (A : ℝ) (hA : 0 ≤ A) :
    (∫ z : UpperHalfPlane, UpperHalfPlane.petersson (k : ℤ)
      (spectralPeterssonStripCutSeed m A) (spectralPeterssonStripCutSeed n A) z) =
      if m = n then (spectralPeterssonTruncatedMass k n A : ℂ) else 0 := by
  let V := spectralPeterssonCutPairRadial k m n A
  let G (p : ℝ × ℝ) : ℂ := cutHorizontal m n p.1*(p.2^2*V p.2 : ℝ)
  let S := (univ : Set ℝ) ×ˢ Ioi (0 : ℝ)
  have hS : {p : ℝ × ℝ | 0 < p.2} = S := by ext p; simp [S]
  have he : (fun z : UpperHalfPlane => UpperHalfPlane.petersson (k : ℤ)
      (spectralPeterssonStripCutSeed m A) (spectralPeterssonStripCutSeed n A) z) =
      fun z : UpperHalfPlane => G (z.re,z.im) := by
    funext z
    exact spectralPeterssonStripCut_pair_coordinates k hk m n A z
  rw [he,upperHalfPlane_integral_coordinates_smul]
  calc
    _ = ∫ p in S, cutHorizontal m n p.1*(V p.2 : ℂ) := by
      rw [hS]
      apply setIntegral_congr_fun ((MeasurableSet.univ : MeasurableSet (univ : Set ℝ)).prod measurableSet_Ioi)
      intro p hp
      have hy : p.2 ≠ 0 := (show 0 < p.2 from hp.2).ne'
      dsimp only [G]
      rw [Complex.real_smul]
      push_cast
      field_simp [hy]
    _ = (∫ x, cutHorizontal m n x)*(∫ y in Ioi (0 : ℝ), (V y : ℂ)) := by
      change (∫ p in (univ : Set ℝ) ×ˢ Ioi (0 : ℝ), cutHorizontal m n p.1*(V p.2 : ℂ) ∂(volume.prod volume)) = _
      simpa only [setIntegral_univ] using! (setIntegral_prod_mul
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (cutHorizontal m n) (fun y => (V y : ℂ)) (univ : Set ℝ) (Ioi (0 : ℝ)))
    _ = _ := by
      rw [cutHorizontal_integral]
      by_cases hmn : m = n
      · subst n
        simp only [ite_true,one_mul]
        rw [integral_complex_ofReal]
        simpa only [V] using congrArg Complex.ofReal (spectralPeterssonCutPairRadial_diagonal k m A hA)
      · simp only [hmn,ite_false,zero_mul]

end ArtinMatthews
