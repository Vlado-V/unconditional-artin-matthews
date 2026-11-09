module

public import ArtinMatthews.SpectralGamma0EllipticTests


set_option backward.privateInPublic true
@[expose] public section

/-! Exact local coordinate conversion for the real and imaginary components
of a smooth native representative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ArtinMatthews

def spectralEllipticPlaneComponents (u v : (Fin 2 → ℝ) → ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.equivRealProdCLM.symm
    (u (spectralEllipticCoordinates.symm p),v (spectralEllipticCoordinates.symm p))

theorem spectralEllipticPlaneComponents_contDiffOn
    (u v : (Fin 2 → ℝ) → ℝ) {Ω : Set (Fin 2 → ℝ)}
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω) :
    ContDiffOn ℝ ∞ (spectralEllipticPlaneComponents u v)
      (spectralEllipticCoordinates.symm ⁻¹' Ω) :=
  Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn
    ((hu.comp spectralEllipticCoordinates.symm.contDiff.contDiffOn (fun _ hx => hx)).prodMk
      (hv.comp spectralEllipticCoordinates.symm.contDiff.contDiffOn (fun _ hx => hx)))

theorem spectralEllipticPlaneComponents_fderiv
    (u v : (Fin 2 → ℝ) → ℝ) {p : ℝ × ℝ}
    (hu : DifferentiableAt ℝ u (spectralEllipticCoordinates.symm p))
    (hv : DifferentiableAt ℝ v (spectralEllipticCoordinates.symm p)) (i : Fin 2) :
    fderiv ℝ (spectralEllipticPlaneComponents u v) p (spectralPlaneDirection i) =
      Complex.equivRealProdCLM.symm
        (fderiv ℝ u (spectralEllipticCoordinates.symm p) (Pi.single i 1),
         fderiv ℝ v (spectralEllipticCoordinates.symm p) (Pi.single i 1)) := by
  have hd := Complex.equivRealProdCLM.symm.hasFDerivAt.comp p
    ((hu.hasFDerivAt.comp p spectralEllipticCoordinates.symm.hasFDerivAt).prodMk
      (hv.hasFDerivAt.comp p spectralEllipticCoordinates.symm.hasFDerivAt))
  change HasFDerivAt (spectralEllipticPlaneComponents u v) _ p at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearEquiv.coe_coe,spectralEllipticCoordinates_symm_direction]

theorem spectralEllipticPlaneComponents_second
    (u v : (Fin 2 → ℝ) → ℝ) {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {p : ℝ × ℝ} (hp : spectralEllipticCoordinates.symm p ∈ Ω) (i : Fin 2) :
    spectralPlaneSecond (spectralEllipticPlaneComponents u v) i p =
      Complex.equivRealProdCLM.symm
        (fderiv ℝ (fun y => fderiv ℝ u y (Pi.single i 1))
            (spectralEllipticCoordinates.symm p) (Pi.single i 1),
         fderiv ℝ (fun y => fderiv ℝ v y (Pi.single i 1))
            (spectralEllipticCoordinates.symm p) (Pi.single i 1)) := by
  let du := fun y => fderiv ℝ u y (Pi.single i 1)
  let dv := fun y => fderiv ℝ v y (Pi.single i 1)
  have he : (fun q => fderiv ℝ (spectralEllipticPlaneComponents u v) q (spectralPlaneDirection i))
      =ᶠ[nhds p] spectralEllipticPlaneComponents du dv := by
    filter_upwards [(hΩ.preimage spectralEllipticCoordinates.symm.continuous).mem_nhds hp] with q hq
    exact spectralEllipticPlaneComponents_fderiv u v
      ((hu.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp))
      ((hv.contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)) i
  have hdu : DifferentiableAt ℝ du (spectralEllipticCoordinates.symm p) :=
    (((hu.contDiffAt (hΩ.mem_nhds hp)).fderiv_right (m := 1) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hdv : DifferentiableAt ℝ dv (spectralEllipticCoordinates.symm p) :=
    (((hv.contDiffAt (hΩ.mem_nhds hp)).fderiv_right (m := 1) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  unfold spectralPlaneSecond
  rw [he.fderiv_eq]
  exact spectralEllipticPlaneComponents_fderiv du dv hdu hdv i

theorem spectralEllipticPlaneComponents_laplacian
    (u v : (Fin 2 → ℝ) → ℝ) {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {p : ℝ × ℝ} (hp : spectralEllipticCoordinates.symm p ∈ Ω) :
    -(p.2^2) • (spectralPlaneSecond (spectralEllipticPlaneComponents u v) 0 p +
        spectralPlaneSecond (spectralEllipticPlaneComponents u v) 1 p) =
      Complex.equivRealProdCLM.symm
        (p.2^2*spectralEllipticPositiveLaplacian u (spectralEllipticCoordinates.symm p),
         p.2^2*spectralEllipticPositiveLaplacian v (spectralEllipticCoordinates.symm p)) := by
  rw [spectralEllipticPlaneComponents_second u v hΩ hu hv hp 0,
    spectralEllipticPlaneComponents_second u v hΩ hu hv hp 1,← map_add,← map_smul]
  congr 1
  simp only [Prod.mk_add_mk,Prod.smul_mk,smul_eq_mul]
  apply Prod.ext
  · simp only [spectralEllipticPositiveLaplacian,Fin.sum_univ_two]
    ring
  · simp only [spectralEllipticPositiveLaplacian,Fin.sum_univ_two]
    ring

end ArtinMatthews
