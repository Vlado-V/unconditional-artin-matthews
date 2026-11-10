module

public import ArtinMatthews.CubicThetaSiegelTransform
public import OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized Siegel square-root multiplier has one constant sign on
the Eisenstein upper-half-plane line. This removes branch ambiguity without
assuming any finite Weil eigenvalue or modularity. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane
open scoped MatrixGroups
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-- The classical weight-one factor never vanishes on the upper half plane. -/
theorem eisensteinClassicalFactor_ne_zero (γ : SL(2, ℚ)) (τ : ℍ) :
    (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) ≠ 0 := by
  have h := (realBlocks (eisensteinSymplectic γ)).denominator_det_isUnit
    (eisensteinSiegel τ)
  rw [eisensteinSiegel_denominator_det] at h
  exact fun hz => h.ne_zero (by simp [hz])

/-- The square-root multiplier restricted to the Eisenstein line is continuous. -/
theorem eisensteinHalfDet_continuous (γ : SL(2, ℚ)) :
    Continuous (fun τ : ℍ => halfDet (realBlocks (eisensteinSymplectic γ))
      (eisensteinSiegel τ)) := by
  have he : Continuous (fun τ : ℍ => ofSiegel (eisensteinSiegel τ)) := by
    apply Continuous.subtype_mk
    change Continuous (fun τ : ℍ => eisensteinSiegelMatrix τ)
    unfold eisensteinSiegelMatrix
    fun_prop
  exact (halfDetDomain_continuous (realBlocks (eisensteinSymplectic γ))).comp he

/-- The sign is fixed by the value at the point `i`. -/
def eisensteinHalfDetSign (γ : SL(2, ℚ)) : ℂ :=
  halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel UpperHalfPlane.I) /
    ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ))

theorem eisensteinHalfDetSign_sq (γ : SL(2, ℚ)) :
    eisensteinHalfDetSign γ ^ 2 = 1 := by
  rw [eisensteinHalfDetSign, div_pow, eisensteinSiegel_halfDet_sq,
    div_self (pow_ne_zero _ (eisensteinClassicalFactor_ne_zero γ UpperHalfPlane.I))]

/-- One constant sign accounts for the square-root branch at every point. -/
theorem eisensteinHalfDet_eq_sign_mul (γ : SL(2, ℚ)) (τ : ℍ) :
    halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) =
      eisensteinHalfDetSign γ * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) := by
  have he := OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot.continuous_square_roots_eq
    (fun z : ℍ => halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel z))
    (fun z : ℍ => eisensteinHalfDetSign γ * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)))
    (eisensteinHalfDet_continuous γ) (by fun_prop)
    (fun z => halfDet_ne_zero _ _) (fun z => by
      rw [mul_pow, eisensteinHalfDetSign_sq, one_mul]
      exact eisensteinSiegel_halfDet_sq γ z)
    UpperHalfPlane.I (by
      rw [eisensteinHalfDetSign]
      exact (div_mul_cancel₀ _ (eisensteinClassicalFactor_ne_zero γ UpperHalfPlane.I)).symm)
  exact congrFun he τ

end ArtinMatthews
