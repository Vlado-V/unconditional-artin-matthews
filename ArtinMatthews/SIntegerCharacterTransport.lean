module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.MulChar.Basic
public import ArtinMatthews.ProbeCRTAdditiveComponents
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Exact character transport through a proved ring equivalence. The
trivial character keeps its nonunit mask, so zeroth powers are preserved. -/
namespace ArtinMatthews.SIntegerQuotient

open scoped Classical
noncomputable section
variable {R T C : Type*} [CommRing R] [CommRing T] [CommMonoidWithZero C]

def pullCharacter (e : R ≃+* T) (χ : MulChar T C) : MulChar R C where
  toMonoidHom := χ.toMonoidHom.comp e.toMonoidHom
  map_nonunit' x hx := χ.map_nonunit (by
    intro he
    apply hx
    have hh := he.map e.symm
    change IsUnit (e.symm (e x)) at hh
    rw [e.symm_apply_apply] at hh
    exact hh)

theorem pullCharacter_apply (e : R ≃+* T) (χ : MulChar T C) (x : R) :
    pullCharacter e χ x = χ (e x) := rfl

theorem pullCharacter_one (e : R ≃+* T) : pullCharacter e (1 : MulChar T C) = 1 := by
  ext u
  rw [pullCharacter_apply, MulChar.one_apply_coe]
  exact MulChar.one_apply (u.isUnit.map e)

theorem pullCharacter_mul (e : R ≃+* T) (χ ψ : MulChar T C) :
    pullCharacter e (χ*ψ) = pullCharacter e χ * pullCharacter e ψ := rfl

theorem pullCharacter_pow (e : R ≃+* T) (χ : MulChar T C) (n : ℕ) :
    pullCharacter e (χ^n) = pullCharacter e χ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pullCharacter_one]
  | succ n ih => rw [pow_succ, pow_succ, pullCharacter_mul, ih]

def pullCharacterHom (e : R ≃+* T) : MulChar T C →* MulChar R C where
  toFun := pullCharacter e
  map_one' := pullCharacter_one e
  map_mul' := pullCharacter_mul e

theorem pullCharacter_injective (e : R ≃+* T) : Function.Injective (pullCharacter (C := C) e) := by
  intro χ ψ h
  ext u
  have hv := congrArg (fun φ : MulChar R C => φ (e.symm (u : T))) h
  simpa only [pullCharacter_apply, RingEquiv.apply_symm_apply] using hv

theorem pullCharacter_orderOf (e : R ≃+* T) (χ : MulChar T C) :
    orderOf (pullCharacter e χ) = orderOf χ :=
  orderOf_injective (pullCharacterHom e) (pullCharacter_injective e) χ

def pullAddChar (e : R ≃+* T) (ψ : AddChar T ℂ) : AddChar R ℂ :=
  ψ.compAddMonoidHom e.toAddMonoidHom

theorem pullAddChar_apply (e : R ≃+* T) (ψ : AddChar T ℂ) (x : R) :
    pullAddChar e ψ x = ψ (e x) := rfl

theorem pullAddChar_primitive (e : R ≃+* T) (ψ : AddChar T ℂ) (hψ : ψ.IsPrimitive) :
    (pullAddChar e ψ).IsPrimitive :=
  VaryingKummerAnalytic.probeAddChar_transport_primitive e ψ hψ

theorem pullCharacter_nonunit (e : R ≃+* T) (χ : MulChar T C) (x : R) (hx : ¬ IsUnit x) :
    pullCharacter e χ x = 0 := (pullCharacter e χ).map_nonunit hx

end
end ArtinMatthews.SIntegerQuotient
