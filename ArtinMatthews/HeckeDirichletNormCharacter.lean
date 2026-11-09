module

public import ArtinMatthews.HeckeDirichletNormResidue
public import ArtinMatthews.CubicThetaCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! A Dirichlet character pulled back by the actual ideal norm, represented
as a genuine member of the checked Eisenstein Hecke family. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
local notation "EO" => HeckeFamily.O

private instance : IsPrincipalIdealRing EO :=
  IsCyclotomicExtension.Rat.three_pid HeckeFamily.K

def heckeDirichletNormResidue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    MulChar (CubicThetaResidue q) ℂ where
  toMonoidHom := χ.toMonoidHom.comp (heckeResidueNorm q)
  map_nonunit' r hr := χ.map_nonunit (fun hu => hr ((heckeResidueNorm_isUnit_iff q r).mp hu))

theorem heckeDirichletNormResidue_mk {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : EO) :
    heckeDirichletNormResidue χ (Ideal.Quotient.mk (cubicThetaRationalModulus q) z) =
      χ ((Ideal.span {z}).absNorm : ZMod q) := by
  change χ (heckeResidueNorm q _) = _
  rw [heckeResidueNorm_mk]

theorem heckeDirichletNormResidue_unit_trivial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (u : EOˣ) :
    heckeDirichletNormResidue χ (Ideal.Quotient.mk (cubicThetaRationalModulus q) (u : EO)) = 1 := by
  rw [heckeDirichletNormResidue_mk, Ideal.span_singleton_eq_top.mpr u.isUnit]
  simp

def heckeDirichletNormCharacter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue (cubicThetaRationalModulus q)
    (cubicThetaRationalModulus_ne_bot q) (heckeDirichletNormResidue χ)
    (heckeDirichletNormResidue_unit_trivial χ)

theorem heckeDirichletNormCharacter_modulus_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : (heckeDirichletNormCharacter χ).modulus.absNorm = q^2 := by
  change (cubicThetaRationalModulus q).absNorm = _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact cubicThetaResidue_card q

theorem heckeDirichletNormCharacter_elementCoeff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (z : EO) :
    HeckeFamily.elementCoeff (heckeDirichletNormCharacter χ) z =
      χ ((Ideal.span {z}).absNorm : ZMod q) :=
  heckeDirichletNormResidue_mk χ z

/-- The identity is stated for nonzero ideals. For modulus one the
Dirichlet value at zero is one, whereas an ideal character vanishes there. -/
theorem heckeDirichletNormCharacter_idealCoeff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (I : Ideal EO) (hI : I ≠ 0) :
    thetaIdealCharacter (heckeDirichletNormCharacter χ) I = χ (I.absNorm : ZMod q) := by
  have hz : Submodule.IsPrincipal.generator I ≠ 0 := by
    intro hz
    apply hI
    rw [← Ideal.span_singleton_generator I, hz, Ideal.span_singleton_zero]
    rfl
  rw [← Ideal.span_singleton_generator I,
    thetaIdealCharacter_span (heckeDirichletNormCharacter χ) hz,
    heckeDirichletNormCharacter_elementCoeff]

end ArtinMatthews
