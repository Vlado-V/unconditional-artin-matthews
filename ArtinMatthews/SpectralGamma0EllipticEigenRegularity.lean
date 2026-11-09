module

public import ArtinMatthews.SpectralGamma0EllipticEigenLocal
public import ArtinMatthews.SpectralGamma0EllipticStripPeriod


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine local smooth periodic representatives of the actual full
cuspidal eigenbasis, with their classical coordinate eigen-equation. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_real_smooth_periodic_classical
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (L : ℂ →L[ℝ] ℝ) :
    ∃ u : (Fin 2 → ℝ) → ℝ,
      ContDiffOn ℝ ∞ u (spectralEllipticOpenStrip (2*(N:ℝ)) Y) ∧
      (∀ᵐ y ∂volume, y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
        u y = L (gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0FullCuspidalSpectralBasis N i).val (spectralEllipticCoordinates y))) ∧
      (∀ y ∈ spectralEllipticOpenStrip (N:ℝ) Y, u (y+Pi.single 0 (N:ℝ)) = u y) ∧
      ∀ y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y,
        spectralEllipticPositiveLaplacian u y =
          gamma0AllHeightGradientSpectralValue N i / (y 1)^2 * u y := by
  obtain ⟨u,hu,huf,he⟩ := gamma0FullCuspidalSpectralBasis_real_smooth_classical N i r Y hY L
  exact ⟨u,hu,huf,gamma0CuspTwoCell_real_representative_periodic N r Y hY
    (gamma0FullCuspidalSpectralBasis N i).val L u hu.continuousOn huf,he⟩

theorem gamma0FullCuspidalSpectralBasis_complex_smooth_periodic_components
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ F : (Fin 2 → ℝ) → ℂ,
      ContDiffOn ℝ ∞ F (spectralEllipticOpenStrip (2*(N:ℝ)) Y) ∧
      (∀ᵐ y ∂volume, y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y →
        F y = gamma0CuspTwoCellCoordinateRestriction N r Y hY
          (gamma0FullCuspidalSpectralBasis N i).val (spectralEllipticCoordinates y)) ∧
      (∀ y ∈ spectralEllipticOpenStrip (N:ℝ) Y, F (y+Pi.single 0 (N:ℝ)) = F y) ∧
      ∀ y ∈ spectralEllipticOpenStrip (2*(N:ℝ)) Y,
        spectralEllipticPositiveLaplacian (fun z => (F z).re) y =
          gamma0AllHeightGradientSpectralValue N i / (y 1)^2 * (F y).re ∧
        spectralEllipticPositiveLaplacian (fun z => (F z).im) y =
          gamma0AllHeightGradientSpectralValue N i / (y 1)^2 * (F y).im := by
  obtain ⟨u,hu,huf,hup,huPDE⟩ :=
    gamma0FullCuspidalSpectralBasis_real_smooth_periodic_classical N i r Y hY Complex.reCLM
  obtain ⟨v,hv,hvf,hvp,hvPDE⟩ :=
    gamma0FullCuspidalSpectralBasis_real_smooth_periodic_classical N i r Y hY Complex.imCLM
  let F : (Fin 2 → ℝ) → ℂ := fun x => (u x:ℂ)+(v x:ℂ)*Complex.I
  have hre : (fun x => (F x).re) = u := by funext x; simp [F]
  have him : (fun x => (F x).im) = v := by funext x; simp [F]
  refine ⟨F,(Complex.ofRealCLM.contDiff.comp_contDiffOn hu).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn hv).mul contDiffOn_const),?_,?_,?_⟩
  · filter_upwards [huf,hvf] with x hx hy
    intro hxΩ
    change (u x:ℂ)+(v x:ℂ)*Complex.I = _
    rw [hx hxΩ,hy hxΩ]
    exact Complex.re_add_im _
  · intro x hx
    change (u (x+Pi.single 0 (N:ℝ)):ℂ)+(v (x+Pi.single 0 (N:ℝ)):ℂ)*Complex.I = _
    rw [hup x hx,hvp x hx]
  · intro x hx
    rw [hre,him,congrFun hre x,congrFun him x]
    exact ⟨huPDE x hx,hvPDE x hx⟩

end ArtinMatthews
