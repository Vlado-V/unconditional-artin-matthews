module

public import ArtinMatthews.SpectralGamma0EllipticCompletion
public import OAI.Analysis.PDE.Weak.Boundary.H1WeakGradient


set_option backward.privateInPublic true
@[expose] public section

/-! The completed localized gradient is the actual distributional derivative
of its localized value.  The source theorem is applied to the proved native
graph-closure membership, not to an assumed weak derivative. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

theorem gamma0EllipticPair_weak_derivative
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ) (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) (j : Fin 2) (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ) :
    (∫ x : Fin 2 → ℝ, ((gamma0EllipticPair φ ha hφ r L N u).2 x) j * χ x) =
      -(∫ x : Fin 2 → ℝ, (gamma0EllipticPair φ ha hφ r L N u).1 x *
        fderiv ℝ χ x (Pi.single j 1)) :=
  H1Zero.weak_derivative (gamma0EllipticPair_mem_H1Zero φ ha hφ r L N u) j χ hχ hcχ

end ArtinMatthews
