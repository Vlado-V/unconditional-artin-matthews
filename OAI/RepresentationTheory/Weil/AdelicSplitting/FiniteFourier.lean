module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization
public import OAI.RepresentationTheory.Weil.AdelicSplitting.Assembly
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.AdelicSplitting.NontrivialLocalCharacter
public import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationNonvanishing


set_option backward.privateInPublic true
@[expose] public section

/-! # Finite Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourier.Construction

noncomputable section

/-! The raw Fourier oscillator and exact self-dual inversion at every finite
completion, using character nontriviality forced by the supplied normalization. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanNormalization.LocalAnalysis

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

local instance (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) :=
  ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

theorem normalized_finite_fourier_mem
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
    (n m : ℕ) (hN : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
    (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
    (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
      f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v))
      (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).IsAddHaarMeasure :=
    NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D (.inr v) hN
  let : (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)
      (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).IsAddHaarMeasure := by
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance
  exact NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_fourier_mem _
    (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inr v)) _ f

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

include D hN in
theorem normalized_finite_fourier_inversion
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
      (Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
        (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
        f.val) x = f.val (-x) :=
  NonarchimedeanNormalization.LocalAnalysis.nonarchimedean_fourier_inversion (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inr v)) (n * m) f x

def normalizedFiniteFourierOscillator : Vacuum.Construction.CoverAt F (n * m) C.ψ (.inr v) :=
  NonarchimedeanNormalization.LocalAnalysis.nonarchimedeanRawFourierOscillator (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
    (Characters.Construction.localAdditiveCharacter_unitary F C.ψ C.ψ_unitary (.inr v))
    (Characters.Construction.localAdditiveCharacter_continuous F C.ψ C.ψ_continuous (.inr v))
    (NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inr v)) (n * m)

theorem normalizedFiniteFourierOscillator_covers :
    Vacuum.Construction.projectionAt F (n * m) C.ψ (.inr v)
      (normalizedFiniteFourierOscillator F d hd n m hN H K C P D v) =
        Local.Generators.Construction.weylSymplectic (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) := rfl

theorem normalizedFiniteFourierOscillator_apply
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) (x : Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)) :
    (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
      (normalizedFiniteFourierOscillator F d hd n m hN H K C P D v) f).val x =
        Local.FunctionsMetaplectic.Construction.fourierIntegral (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))
          (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ (.inr v)))
          f.val x := rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteFourier.Construction
