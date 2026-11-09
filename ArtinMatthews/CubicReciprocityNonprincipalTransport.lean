module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact transport of nonprincipal residue characters between ring models. -/

namespace ArtinMatthews

/-- Pull back a multiplicative residue character along a ring isomorphism. -/
noncomputable def residueCharacterPullback {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (χ : MulChar T ℂ) : MulChar R ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp
  map_nonunit' x hx := by
    apply χ.map_nonunit
    intro hu
    have hh := hu.map e.symm.toMonoidHom
    exact hx (by simpa using hh)

@[simp] theorem residueCharacterPullback_apply {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (χ : MulChar T ℂ) (x : R) :
    residueCharacterPullback e χ x = χ (e x) := rfl

@[simp] theorem residueCharacterPullback_one {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) : residueCharacterPullback e (1 : MulChar T ℂ) = 1 := by
  apply MulChar.ext
  intro u
  change (1 : MulChar T ℂ) (e (u : R)) = (1 : MulChar R ℂ) (u : R)
  have hu : IsUnit (e (u : R)) := by simp
  rw [MulChar.one_apply hu, MulChar.one_apply u.isUnit]

theorem residueCharacterPullback_pow {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) (χ : MulChar T ℂ) (n : ℕ) :
    residueCharacterPullback e χ ^ n = residueCharacterPullback e (χ ^ n) := by
  apply MulChar.ext
  intro u
  change (residueCharacterPullback e χ ^ n) (u : R) = (χ ^ n) (e (u : R))
  rw [MulChar.pow_apply_coe]
  exact (MulChar.pow_apply_coe χ n (Units.map e.toMonoidHom u)).symm

/-- Nonprincipality is preserved under the actual residue-ring isomorphism. -/
theorem residueCharacterPullback_ne_one {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) {χ : MulChar T ℂ} (hχ : χ ≠ 1) :
    residueCharacterPullback e χ ≠ 1 := by
  intro h
  apply hχ
  apply MulChar.ext
  intro u
  have hu : IsUnit (e.symm (u : T)) := by
    have hh := u.isUnit.map e.symm.toMonoidHom
    exact hh
  have hh := congrArg (fun ψ : MulChar R ℂ => ψ (e.symm (u : T))) h
  simpa only [residueCharacterPullback_apply, RingEquiv.apply_symm_apply,
    MulChar.one_apply hu, MulChar.one_apply u.isUnit] using hh

@[simp] theorem residueCharacterPullback_eq_one_iff {R T : Type*}
    [CommRing R] [CommRing T] (e : R ≃+* T) (χ : MulChar T ℂ) :
    residueCharacterPullback e χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    by_contra hn
    exact residueCharacterPullback_ne_one e hn h
  · intro h
    rw [h, residueCharacterPullback_one]

end ArtinMatthews
