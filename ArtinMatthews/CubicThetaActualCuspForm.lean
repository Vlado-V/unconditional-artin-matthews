module

public import ArtinMatthews.CubicThetaActualCuspFormBase
public import ArtinMatthews.CubicThetaActualTransformation
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic numerator Hecke theta as a native weight-one cusp form.
The modularity field is supplied by the proved finite/real Weil calculation. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups Topology Manifold
open Complex UpperHalfPlane ModularForm OnePoint CongruenceSubgroup
open OAI OAI.SevenEighths
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- Every allowed enlarged period gives the literal Hecke theta a native
cusp-form structure on the exact kernel of its quadratic nebentypus. -/
def cubicNumeratorHeckeThetaCuspFormOfPeriod
    (D : WeilData (Fin 2) MpR MpF MpA)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (heven : 2 ∣ M) (hdiv : 9 * A ∣ (M : ℤ)) :
    CuspForm (cubicThetaKernel (6 * M ^ 2)) 1 where
  toFun := heckeTheta (cubicNumeratorHeckeCharacter A hA)
  slash_action_eq' δ hδ := by
    rcases hδ with ⟨γ, hγ, rfl⟩
    change (heckeTheta (cubicNumeratorHeckeCharacter A hA)) ∣[(1 : ℤ)] γ = _
    have hc : 6 * (M : ℤ) ^ 2 ∣ γ 1 0 := by
      have hh := (Gamma0_mem).mp hγ.1
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hh
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hh
    have hd : (γ 1 1 : ZMod 3) = 1 := ((Gamma1_mem 3 γ).mp hγ.2).2.1
    have hψ : cubicThetaNebentypus (γ 1 1) = 1 := by
      simp [cubicThetaNebentypus, hd]
    funext τ
    rw [SL_slash_apply,
      cubicNumeratorHeckeTheta_transform D A hA hnoncube M heven hdiv γ hc τ,
      hψ, one_mul, zpow_neg_one]
    have hden : UpperHalfPlane.denom γ τ =
        (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) := by
      erw [ModularGroup.denom_apply]
    have hn : (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) ≠ 0 :=
      hden ▸ UpperHalfPlane.denom_ne_zero γ τ
    rw [hden]
    field_simp [hn]
  holo' := heckeTheta_mdiff _
  zero_at_cusps' hc := cubicNumeratorHeckeTheta_zeroAt_cusp A hA hnoncube _ hc

@[simp] theorem cubicNumeratorHeckeThetaCuspFormOfPeriod_apply
    (D : WeilData (Fin 2) MpR MpF MpA)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (M : ℕ) [NeZero M] (heven : 2 ∣ M) (hdiv : 9 * A ∣ (M : ℤ)) (τ : ℍ) :
    cubicNumeratorHeckeThetaCuspFormOfPeriod D A hA hnoncube M heven hdiv τ =
      heckeTheta (cubicNumeratorHeckeCharacter A hA) τ := rfl

/-- The explicit level-1944|A|² cusp form, with unchanged underlying theta. -/
def cubicNumeratorHeckeThetaCuspForm
    (D : WeilData (Fin 2) MpR MpF MpA)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) :
    CuspForm (cubicThetaKernel (cubicNumeratorThetaLevel A)) 1 := by
  let : NeZero (cubicNumeratorThetaPeriod A) := ⟨cubicNumeratorThetaPeriod_ne_zero hA⟩
  exact cubicNumeratorHeckeThetaCuspFormOfPeriod D A hA hnoncube
    (cubicNumeratorThetaPeriod A) (cubicNumeratorThetaPeriod_even A)
    (cubicNumeratorThetaPeriod_conductor_dvd A)

@[simp] theorem cubicNumeratorHeckeThetaCuspForm_coe
    (D : WeilData (Fin 2) MpR MpF MpA)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) :
    (fun τ => cubicNumeratorHeckeThetaCuspForm D A hA hnoncube τ) =
      heckeTheta (cubicNumeratorHeckeCharacter A hA) := rfl

/-- The packaged cusp form has exactly the actual ideal-norm Fourier sums. -/
theorem cubicNumeratorHeckeThetaCuspForm_qExpansion_coeff
    (D : WeilData (Fin 2) MpR MpF MpA)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein)) (n : ℕ) :
    (qExpansion 1 (cubicNumeratorHeckeThetaCuspForm D A hA hnoncube)).coeff n =
      idealThetaCoeff (cubicNumeratorHeckeCharacter A hA) n :=
  heckeTheta_qExpansion_coeff _ n

end ArtinMatthews
