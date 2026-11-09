module

public import ArtinMatthews.AdelicCharacterData
public import ArtinMatthews.BareArchimedeanFourier
public import ArtinMatthews.CompletionNondiscrete
public import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner
public import OAI.RepresentationTheory.Weil.Local.Analytic


set_option backward.privateInPublic true
@[expose] public section

/-! Construct the actual local Fourier oscillator directly from the local
analytic normalization.  No normalized unitary-splitting datum is supplied. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

local instance bareLocalAdicMeasurable (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance bareLocalAdicBorel (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩


variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
  (d : AdelicCharacterData F ψ) (N : ℕ)

include d in
theorem character_positionHaar (v : ArchimedeanAdeles.Construction.Places F) :
    (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
      (ArchimedeanAdeles.Construction.Completion F v) N
      (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure := by
  let : SecondCountableTopology (ArchimedeanAdeles.Construction.Completion F v) :=
    OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable
      _ (completion_nondiscrete F v)
  have h := OAI.RepresentationTheory.Weil.Local.Analytic.Construction.localField_analytic_normalization
    (completion_nondiscrete F v)
    (Characters.Construction.localAdditiveCharacter F ψ v)
    (AdelicCharacterData.local_continuous F ψ d v) (AdelicCharacterData.local_unitary F ψ d v) (d.local_nontrivial v) N
  let : (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure
      (ArchimedeanAdeles.Construction.Completion F v)
      (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure := h.2.1
  unfold OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
  infer_instance

include d in
theorem bare_fourier_analysis (v : ArchimedeanAdeles.Construction.Places F) :
    (∀ f : OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat
        (ArchimedeanAdeles.Construction.Completion F v) N,
      OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral
        (Characters.Construction.localAdditiveCharacter F ψ v)
        (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
          (ArchimedeanAdeles.Construction.Completion F v) N
          (Characters.Construction.localAdditiveCharacter F ψ v)) f.val ∈
        OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat
          (ArchimedeanAdeles.Construction.Completion F v) N) ∧
    ∀ (f : OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat
        (ArchimedeanAdeles.Construction.Completion F v) N) x,
      OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral
        (Characters.Construction.localAdditiveCharacter F ψ v)
        (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
          (ArchimedeanAdeles.Construction.Completion F v) N
          (Characters.Construction.localAdditiveCharacter F ψ v))
        (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral
          (Characters.Construction.localAdditiveCharacter F ψ v)
          (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
            (ArchimedeanAdeles.Construction.Completion F v) N
            (Characters.Construction.localAdditiveCharacter F ψ v)) f.val) x = f.val (-x) := by
  let : (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
      (ArchimedeanAdeles.Construction.Completion F v) N
      (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure :=
    character_positionHaar F ψ d N v
  cases v with
  | inl v =>
      exact BareArchimedean.archimedean_fourier_analysis F N v _
        (AdelicCharacterData.local_continuous F ψ d (.inl v)) (AdelicCharacterData.local_unitary F ψ d (.inl v)) (d.local_nontrivial (.inl v))
  | inr v =>
      exact ⟨OAI.RepresentationTheory.Weil.Local.CompactCharacter.Construction.nonarchimedean_fourier_mem
        (completion_nondiscrete F (.inr v)) _
        (AdelicCharacterData.local_unitary F ψ d (.inr v)) (AdelicCharacterData.local_continuous F ψ d (.inr v))
        (d.local_nontrivial (.inr v)) _,
        OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalization.Construction.nonarchimedean_fourier_inversion_selfDual
          (completion_nondiscrete F (.inr v)) N _
          (AdelicCharacterData.local_unitary F ψ d (.inr v)) (AdelicCharacterData.local_continuous F ψ d (.inr v))
          (d.local_nontrivial (.inr v))⟩

def bareFourierAt (v : ArchimedeanAdeles.Construction.Places F) : Vacuum.Construction.CoverAt F N ψ v := by
  let : SecondCountableTopology (ArchimedeanAdeles.Construction.Completion F v) :=
    OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable
      _ (completion_nondiscrete F v)
  let : (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
      (ArchimedeanAdeles.Construction.Completion F v) N
      (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure :=
    character_positionHaar F ψ d N v
  let h := bare_fourier_analysis F ψ d N v
  exact FourierIntertwiner.LocalAnalysis.fourierOscillator _ (AdelicCharacterData.local_unitary F ψ d v)
    (AdelicCharacterData.local_continuous F ψ d v) _ h.1 h.2

theorem bareFourierAt_covers (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F N ψ v (bareFourierAt F ψ d N v) =
      OAI.RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic
        (ArchimedeanAdeles.Construction.Completion F v) N := rfl

theorem bareFourierAt_apply (v : ArchimedeanAdeles.Construction.Places F)
    (f : OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat
      (ArchimedeanAdeles.Construction.Completion F v) N)
    (x : OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position
      (ArchimedeanAdeles.Construction.Completion F v) N) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N
      (Characters.Construction.localAdditiveCharacter F ψ v) (bareFourierAt F ψ d N v) f).val x =
      OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.fourierIntegral
        (Characters.Construction.localAdditiveCharacter F ψ v)
        (OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.positionMeasure
          (ArchimedeanAdeles.Construction.Completion F v) N
          (Characters.Construction.localAdditiveCharacter F ψ v)) f.val x := rfl

theorem bareFourierAt_rational_covers (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F N ψ v (bareFourierAt F ψ d N v) =
      Vacuum.Construction.rationalSymplecticLocal F N v
        (OAI.RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic F N) := by
  rw [bareFourierAt_covers]
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [Vacuum.Construction.rationalSymplecticLocal, Vacuum.Construction.mapSymplectic,
      OAI.RepresentationTheory.Weil.Local.Generators.Construction.weylSymplectic_matrix,
      Matrix.fromBlocks, Matrix.map_apply, Matrix.one_apply]

end

end ArtinMatthews.QuadraticWeil
