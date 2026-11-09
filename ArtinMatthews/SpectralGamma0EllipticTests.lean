module

public import ArtinMatthews.SpectralGamma0EllipticCoordinates
public import ArtinMatthews.SpectralPlaneTestSeed
public import ArtinMatthews.SpectralSectionLaplacian


set_option backward.privateInPublic true
@[expose] public section

/-! Actual native-coordinate real tests become genuine compact hyperbolic
seeds.  Their coordinate Laplacian is computed from two genuine derivatives. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

def spectralEllipticTestPlane (χ : (Fin 2 → ℝ) → ℝ) (p : ℝ × ℝ) : ℂ :=
  (χ (spectralEllipticCoordinates.symm p) : ℂ)

theorem spectralEllipticTestPlane_smooth (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (spectralEllipticTestPlane χ) :=
  Complex.ofRealCLM.contDiff.comp (hχ.comp spectralEllipticCoordinates.symm.contDiff)

theorem spectralEllipticTestPlane_compact (χ : (Fin 2 → ℝ) → ℝ)
    (hc : HasCompactSupport χ) : HasCompactSupport (spectralEllipticTestPlane χ) :=
  (hc.comp_homeomorph spectralEllipticCoordinates.symm.toHomeomorph).comp_left
    (show ((0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero)

theorem spectralEllipticTestPlane_support (χ : (Fin 2 → ℝ) → ℝ) :
    tsupport (spectralEllipticTestPlane χ) ⊆
      spectralEllipticCoordinates.symm ⁻¹' tsupport χ := by
  apply closure_minimal _ ((isClosed_tsupport χ).preimage spectralEllipticCoordinates.symm.continuous)
  intro p hp
  apply subset_tsupport χ
  change χ (spectralEllipticCoordinates.symm p) ≠ 0
  intro hz
  exact hp (by simp only [spectralEllipticTestPlane,hz,Complex.ofReal_zero])

theorem spectralEllipticTestPlane_positive (χ : (Fin 2 → ℝ) → ℝ)
    (hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1}) :
    tsupport (spectralEllipticTestPlane χ) ⊆ {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  exact hh (spectralEllipticTestPlane_support χ hp)

def spectralEllipticTestSeed (χ : (Fin 2 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1}) :
    h2SmoothCompactSeeds :=
  h2SmoothSeedOfPlane (spectralEllipticTestPlane χ) (spectralEllipticTestPlane_smooth χ hχ)
    (spectralEllipticTestPlane_compact χ hc) (spectralEllipticTestPlane_positive χ hh)

theorem spectralEllipticTestSeed_apply (χ : (Fin 2 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1})
    (z : UpperHalfPlane) :
    (spectralEllipticTestSeed χ hχ hc hh).val z =
      (χ (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ) := rfl

theorem spectralEllipticTestSeed_support (χ : (Fin 2 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1}) :
    tsupport (spectralEllipticTestSeed χ hχ hc hh).val ⊆
      {z : UpperHalfPlane | spectralEllipticCoordinates.symm (z.re,z.im) ∈ tsupport χ} := by
  intro z hz
  apply spectralEllipticTestPlane_support χ
  exact h2SmoothSeedOfPlane_support (spectralEllipticTestPlane χ)
    (spectralEllipticTestPlane_smooth χ hχ) (spectralEllipticTestPlane_compact χ hc)
    (spectralEllipticTestPlane_positive χ hh) hz

theorem spectralEllipticCoordinates_symm_direction (i : Fin 2) :
    spectralEllipticCoordinates.symm (spectralPlaneDirection i) = Pi.single i 1 := by
  rw [← spectralEllipticCoordinates_single,spectralEllipticCoordinates.symm_apply_apply]

theorem spectralEllipticTestPlane_fderiv (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (p : ℝ × ℝ) (i : Fin 2) :
    fderiv ℝ (spectralEllipticTestPlane χ) p (spectralPlaneDirection i) =
      (fderiv ℝ χ (spectralEllipticCoordinates.symm p) (Pi.single i 1) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp p
    (((hχ.differentiable (by simp) (spectralEllipticCoordinates.symm p)).hasFDerivAt).comp p
      spectralEllipticCoordinates.symm.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ χ ∘ spectralEllipticCoordinates.symm) p
    (spectralPlaneDirection i) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    spectralEllipticCoordinates_symm_direction,Complex.ofRealCLM_apply]

def spectralEllipticPositiveLaplacian (χ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  -(∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ χ y (Pi.single i 1)) x (Pi.single i 1))

theorem spectralEllipticTestPlane_second (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (p : ℝ × ℝ) (i : Fin 2) :
    spectralPlaneSecond (spectralEllipticTestPlane χ) i p =
      (fderiv ℝ (fun y => fderiv ℝ χ y (Pi.single i 1))
        (spectralEllipticCoordinates.symm p) (Pi.single i 1) : ℂ) := by
  unfold spectralPlaneSecond
  simp_rw [spectralEllipticTestPlane_fderiv χ hχ]
  exact spectralEllipticTestPlane_fderiv (fun y => fderiv ℝ χ y (Pi.single i 1))
    ((hχ.fderiv_right (by simp)).clm_apply contDiff_const) p i

theorem spectralEllipticTestSeed_laplacian (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1}) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (spectralEllipticTestSeed χ hχ hc hh).val z =
      (z.im^2 * spectralEllipticPositiveLaplacian χ
        (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ) := by
  change h2SectionPositiveLaplacian (fun w => spectralEllipticTestPlane χ (w.re,w.im)) z = _
  rw [h2SectionPositiveLaplacian_representation _ (spectralEllipticTestPlane χ) (fun _ => rfl)]
  simp only [spectralPlanePositiveHyperbolic,spectralPlanePositiveSecond,
    spectralEllipticTestPlane_second χ hχ,spectralEllipticPositiveLaplacian,
    Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_sum,Complex.real_smul]

end ArtinMatthews
