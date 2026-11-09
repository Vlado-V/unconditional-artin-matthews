module

public import ArtinMatthews.SpectralGamma0EllipticTests


set_option backward.privateInPublic true
@[expose] public section

/-! Native compact tests remain smooth and compact under their literal
positive Euclidean Laplacian, with no enlargement of support. -/
noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

theorem spectralEllipticPositiveLaplacian_smooth (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (spectralEllipticPositiveLaplacian χ) := by
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ χ y (Pi.single i 1)) :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  exact (hd.fderiv_right (by simp)).clm_apply contDiff_const

theorem spectralEllipticPositiveLaplacian_support (χ : (Fin 2 → ℝ) → ℝ) :
    tsupport (spectralEllipticPositiveLaplacian χ) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz : ∀ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ χ y (Pi.single i 1)) x = 0 := by
    intro i
    apply fderiv_of_notMem_tsupport
    exact fun hi => hn (tsupport_fderiv_apply_subset ℝ (Pi.single i 1) hi)
  apply hx
  simp only [spectralEllipticPositiveLaplacian,hz,zero_apply,
    Finset.sum_const_zero,neg_zero]

theorem spectralEllipticPositiveLaplacian_compact (χ : (Fin 2 → ℝ) → ℝ)
    (hc : HasCompactSupport χ) : HasCompactSupport (spectralEllipticPositiveLaplacian χ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (spectralEllipticPositiveLaplacian_support χ)

end ArtinMatthews
