module

public import ArtinMatthews.AdicConductorBridge
public import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters


set_option backward.privateInPublic true
@[expose] public section

/-! Natural analytic/conductor properties of an actual adelic additive
character.  This record contains no Fourier family, splitting datum, or
Weil-product identity. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain Filter
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

structure AdelicCharacterData (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) : Prop where
  continuous : Continuous ψ
  unitary : ∀ x, ‖ψ x‖ = 1
  principal : ∀ x : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) x) = 1
  local_nontrivial : ∀ v : ArchimedeanAdeles.Construction.Places F,
    ∃ x : ArchimedeanAdeles.Construction.Completion F v,
      Characters.Construction.localAdditiveCharacter F ψ v x ≠ 1
  conductor_zero : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    adicConductorZero F v (Characters.Construction.localAdditiveCharacter F ψ (.inr v))

theorem AdelicCharacterData.local_continuous
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (d : AdelicCharacterData F ψ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    Continuous (Characters.Construction.localAdditiveCharacter F ψ v) :=
  Characters.Construction.localAdditiveCharacter_continuous F ψ d.continuous v

theorem AdelicCharacterData.local_unitary
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (d : AdelicCharacterData F ψ)
    (v : ArchimedeanAdeles.Construction.Places F) (x : ArchimedeanAdeles.Construction.Completion F v) :
    ‖Characters.Construction.localAdditiveCharacter F ψ v x‖ = 1 :=
  Characters.Construction.localAdditiveCharacter_unitary F ψ d.unitary v x

end

end ArtinMatthews.QuadraticWeil
