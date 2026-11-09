module

public import ArtinMatthews.SpectralGamma0EllipticEigenRegularity
public import ArtinMatthews.SpectralGamma0EllipticPlaneComponents


set_option backward.privateInPublic true
@[expose] public section

/-! The literal plane-coordinate smooth cusp representative and classical
eigen-equation consumed by the local Fourier/Bessel adapter. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_plane_smooth_periodic_classical
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ F : (ℝ × ℝ) → ℂ,
      ContDiffOn ℝ ∞ F {p | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2} ∧
      (∀ᵐ p ∂volume, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
        F p = gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0FullCuspidalSpectralBasis N i).val p) ∧
      (∀ p : ℝ × ℝ, (0 < p.1 ∧ p.1 < (N:ℝ) ∧ Y < p.2) →
        F (p.1+(N:ℝ),p.2) = F p) ∧
      ∀ p : ℝ × ℝ, (0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2) →
        -(p.2^2) • (spectralPlaneSecond F 0 p + spectralPlaneSecond F 1 p) =
          (gamma0AllHeightGradientSpectralValue N i : ℂ)*F p := by
  obtain ⟨u,hu,huf,hup,huPDE⟩ :=
    gamma0FullCuspidalSpectralBasis_real_smooth_periodic_classical N i r Y hY Complex.reCLM
  obtain ⟨v,hv,hvf,hvp,hvPDE⟩ :=
    gamma0FullCuspidalSpectralBasis_real_smooth_periodic_classical N i r Y hY Complex.imCLM
  let F := spectralEllipticPlaneComponents u v
  have hpre : spectralEllipticCoordinates.symm ⁻¹' spectralEllipticOpenStrip (2*(N:ℝ)) Y =
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 2*(N:ℝ) ∧ Y < p.2} := by
    ext p
    rfl
  refine ⟨F,?_,?_,?_,?_⟩
  · rw [← hpre]
    exact spectralEllipticPlaneComponents_contDiffOn u v hu hv
  · have huf' := spectralEllipticCoordinates_symm_measurePreserving.quasiMeasurePreserving.ae huf
    have hvf' := spectralEllipticCoordinates_symm_measurePreserving.quasiMeasurePreserving.ae hvf
    filter_upwards [huf',hvf'] with p hp hq
    intro hpΩ
    have hpn : spectralEllipticCoordinates.symm p ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y := hpΩ
    change Complex.equivRealProdCLM.symm
      (u (spectralEllipticCoordinates.symm p),v (spectralEllipticCoordinates.symm p)) = _
    rw [hp hpn,hq hpn,ContinuousLinearEquiv.apply_symm_apply]
    exact Complex.equivRealProdCLM.symm_apply_apply _
  · intro p hp
    have hpn : spectralEllipticCoordinates.symm p ∈ spectralEllipticOpenStrip (N:ℝ) Y := hp
    have hshift : spectralEllipticCoordinates.symm (p.1+(N:ℝ),p.2) =
        spectralEllipticCoordinates.symm p+Pi.single 0 (N:ℝ) := by
      ext j
      fin_cases j
      · rfl
      · change p.2 = p.2+0
        exact (add_zero p.2).symm
    change Complex.equivRealProdCLM.symm
      (u (spectralEllipticCoordinates.symm (p.1+(N:ℝ),p.2)),
        v (spectralEllipticCoordinates.symm (p.1+(N:ℝ),p.2))) = _
    rw [hshift,hup _ hpn,hvp _ hpn]
    rfl
  · intro p hp
    have hpn : spectralEllipticCoordinates.symm p ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y := hp
    have hheight : (spectralEllipticCoordinates.symm p) 1 = p.2 := rfl
    have hp0 : p.2 ≠ 0 := (hY.trans hp.2.2).ne'
    rw [spectralEllipticPlaneComponents_laplacian u v (spectralEllipticOpenStrip_isOpen _ _)
      hu hv hpn,huPDE _ hpn,hvPDE _ hpn,hheight]
    have hcancel (z : ℝ) : p.2^2*(gamma0AllHeightGradientSpectralValue N i / p.2^2*z) =
        gamma0AllHeightGradientSpectralValue N i*z := by field_simp [hp0]
    rw [hcancel,hcancel,← Complex.real_smul]
    change Complex.equivRealProdCLM.symm
        (gamma0AllHeightGradientSpectralValue N i •
          (u (spectralEllipticCoordinates.symm p),v (spectralEllipticCoordinates.symm p))) = _
    exact map_smul _ _ _

end ArtinMatthews
