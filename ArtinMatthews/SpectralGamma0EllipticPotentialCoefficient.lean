module

public import ArtinMatthews.SpectralGamma0EllipticPotentialFunction
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded


set_option backward.privateInPublic true
@[expose] public section

/-! A globally smooth bounded multiplication operator which agrees with
the actual eigenfunction potential on the cutoff plateau. -/
noncomputable section
open Set
open scoped ContDiff
open OAI.Analysis.PDE.Weak
namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

def spectralEllipticPotentialCoefficient (lam : ℝ) :
    (Fin 2 → ℝ) → ℝ →L[ℝ] ℝ :=
  fun x => spectralEllipticPotentialFunction φ ha hφ lam x • ContinuousLinearMap.id ℝ ℝ

theorem spectralEllipticPotentialCoefficient_smoothBounded (lam : ℝ) :
    SmoothBounded (spectralEllipticPotentialCoefficient φ ha hφ lam) :=
  smoothBounded_of_hasCompactSupport
    ((spectralEllipticPotentialFunction_smooth φ ha hφ lam).smul contDiff_const)
    ((spectralEllipticPotentialFunction_compact φ ha hφ lam).smul_right)

theorem spectralEllipticPotentialCoefficient_apply_eq (lam : ℝ) {x : Fin 2 → ℝ}
    (hx : 0 < x 1) (hplateau : φ (spectralEllipticCoordinates x) = 1) (u : ℝ) :
    spectralEllipticPotentialCoefficient φ ha hφ lam x u = lam / (x 1)^2 * u := by
  change spectralEllipticPotentialFunction φ ha hφ lam x * u = _
  rw [spectralEllipticPotentialFunction_eq φ ha hφ lam hx hplateau]

end ArtinMatthews
