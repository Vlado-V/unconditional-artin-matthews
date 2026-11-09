module

public import ArtinMatthews.CubicThetaWeilTransform
public import ArtinMatthews.CubicThetaHalfDetRatio
public import ArtinMatthews.CubicThetaUnweightedNonzero


set_option backward.privateInPublic true
@[expose] public section

/-! Transfer of the proved unweighted theta multiplier to a finite test
with the same finite-operator scalar. Concrete scalar equalities are inputs
to this intermediate lemma; their arithmetic proof remains separate. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane
open scoped MatrixGroups
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-- Constant residue weights give the same actual unweighted theta at every period. -/
theorem theta_eisensteinFiniteTest_one (M : ℕ) [NeZero M] (τ : ℍ) :
    theta (eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ)))
      (eisensteinSiegel τ) 0 = eisensteinHolomorphicTheta τ := by
  rw [theta_eisensteinFiniteTest, eisensteinHolomorphicTheta_eq_gaussian]
  apply tsum_congr
  intro n
  simp [OAI.SevenEighths.HeckeTheta.periodicCoeff]

/-- Linearity of the actual rational theta sum in its finite test. -/
theorem eisensteinTheta_smul (c : ℂ) (φ : finiteSchwartz (Fin 2)) (τ : ℍ) :
    theta (c • φ) (eisensteinSiegel τ) 0 = c * theta φ (eisensteinSiegel τ) 0 := by
  unfold theta thetaTerm
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- A common finite-operator scalar is uniquely determined by the exact
unweighted multiplier. The square-root sign is handled uniformly on ℍ. -/
theorem eisensteinFinite_scalar_from_unweighted
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℚ))
    (ν : ℂ) (hν : ∀ τ : ℍ, eisensteinHolomorphicTheta (γ • τ) =
      ν * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * eisensteinHolomorphicTheta τ)
    (M : ℕ) [NeZero M] (c : ℂ)
    (hc : D.finiteAction (eisensteinSymplectic γ)
      (eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ))) =
        c • eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ))) :
    c * ν = eisensteinHalfDetSign γ := by
  have h := eisensteinAdelicTheta_transform D γ
    (eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ))) UpperHalfPlane.I
  rw [hc, eisensteinTheta_smul, theta_eisensteinFiniteTest_one,
    theta_eisensteinFiniteTest_one, eisensteinHalfDet_eq_sign_mul, hν] at h
  apply mul_right_cancel₀ (mul_ne_zero
    (eisensteinClassicalFactor_ne_zero γ UpperHalfPlane.I) eisensteinHolomorphicTheta_I_ne_zero)
  calc
    (c * ν) * (((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) *
      eisensteinHolomorphicTheta UpperHalfPlane.I) =
        c * (ν * ((γ 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) + (γ 1 1 : ℂ)) *
          eisensteinHolomorphicTheta UpperHalfPlane.I) := by ring
    _ = _ := h
    _ = _ := by ring

/-- The same finite scalar transports the exact unweighted multiplier to
any finite test. No choice of square-root branch remains. -/
theorem eisensteinTheta_common_scalar_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℚ))
    (ν : ℂ) (hν : ∀ τ : ℍ, eisensteinHolomorphicTheta (γ • τ) =
      ν * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * eisensteinHolomorphicTheta τ)
    (M : ℕ) [NeZero M] (c : ℂ)
    (hbase : D.finiteAction (eisensteinSymplectic γ)
      (eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ))) =
        c • eisensteinFiniteTest (fun _ : Fin M × Fin M => (1 : ℂ)))
    (φ : finiteSchwartz (Fin 2))
    (hφ : D.finiteAction (eisensteinSymplectic γ) φ = c • φ) (τ : ℍ) :
    theta φ (eisensteinSiegel (γ • τ)) 0 =
      ν * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * theta φ (eisensteinSiegel τ) 0 := by
  have he := eisensteinFinite_scalar_from_unweighted D γ ν hν M c hbase
  have hc : c ≠ 0 := by
    intro hz
    have hs := eisensteinHalfDetSign_sq γ
    rw [← he, hz, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    exact zero_ne_one hs
  apply mul_left_cancel₀ hc
  have h := eisensteinAdelicTheta_transform D γ φ τ
  rw [hφ, eisensteinTheta_smul, eisensteinHalfDet_eq_sign_mul, ← he] at h
  calc
    c * theta φ (eisensteinSiegel (γ • τ)) 0 = _ := h
    _ = _ := by ring

end ArtinMatthews
