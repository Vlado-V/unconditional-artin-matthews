module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelFieldTransport
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters
public import OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel
public import OAI.RepresentationTheory.Weil.Local.ComplexCover
public import OAI.RepresentationTheory.Weil.Local.ComplexFieldGaussian
public import OAI.RepresentationTheory.Weil.Local.ComplexFieldNormalization
public import OAI.RepresentationTheory.Weil.Local.ComplexWeyl
public import OAI.RepresentationTheory.Weil.Local.RealFieldEq
public import OAI.RepresentationTheory.Weil.Local.RealNormalization
public import OAI.RepresentationTheory.Weil.Local.RealWeyl


set_option backward.privateInPublic true
@[expose] public section

/-! # Archimedean Fresnel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFresnel.LocalAnalysis

noncomputable section

/-! The exact Gaussian Fourier-quadratic relation in arbitrary real and
complex local field presentations, with the prescribed Gaussian phase. -/

open _root_.MeasureTheory

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]

theorem realField_fresnel (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℝ) (he : Continuous e) (hi : Continuous e.symm)
    (N : ℕ) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ)
      (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ 1 (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f.val)) x =
      Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ N * ψ (-Local.FunctionsMetaplectic.Construction.quadratic 1 x) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x := by
  let η := Local.FieldFourier.Construction.fieldCharacter e ψ
  have hηc : Continuous η := Local.ArchimedeanKernel.Construction.fieldCharacter_continuous e hi ψ hc
  have hηu : ∀ t, ‖η t‖ = 1 := Local.ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hu
  have hηn : ∃ t, η t ≠ 1 := Local.ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hn
  obtain ⟨c, hcz, hη⟩ := RealCharacters.LocalAnalysis.continuous_nontrivial_unitary_real_character η hηc hηu hηn
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ η).IsAddHaarMeasure := (Local.RealNormalization.Construction.real_analytic_normalization η hηc hηu hηn N).2.1
  have hm := (Local.RealFieldEq.Construction.realField_selfDual_normalization e he hi ψ hc hu hn).2.2
  have hγ : Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 = Local.FunctionsMetaplectic.Construction.gaussianIndex ℝ η 1 := by
    simpa only [map_one] using (Local.RealFieldEq.Construction.realField_gaussian_normalization hArch e he hi ψ hc hu hn 1 one_ne_zero).2
  apply FresnelFieldTransport.LocalAnalysis.fresnel_fieldTransport e he hi N ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ) (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ η) hm _ _ f x
  intro g y
  change Local.FunctionsMetaplectic.Construction.fourierIntegral η (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ N η)
    (Local.FunctionsMetaplectic.Construction.quadraticOperator η 1 (Local.FunctionsMetaplectic.Construction.fourierIntegral η (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ N η) g.val)) y =
      Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ N * η (-Local.FunctionsMetaplectic.Construction.quadratic 1 y) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral η (Local.FunctionsMetaplectic.Construction.positionMeasure ℝ N η) (Local.FunctionsMetaplectic.Construction.quadraticOperator η (-1) g.val) y
  rw [hγ, hη]
  exact Local.RealWeyl.Construction.real_fourier_quadratic_fourier c hcz g y

theorem complexField_fresnel (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℂ) (he : Continuous e) (hi : Continuous e.symm)
    (N : ℕ) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ)
      (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ 1 (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) f.val)) x =
      Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ N * ψ (-Local.FunctionsMetaplectic.Construction.quadratic 1 x) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure k N ψ) (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x := by
  let η := Local.FieldFourier.Construction.fieldCharacter e ψ
  have hηc : Continuous η := Local.ArchimedeanKernel.Construction.fieldCharacter_continuous e hi ψ hc
  have hηu : ∀ t, ‖η t‖ = 1 := Local.ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hu
  have hηn : ∃ t, η t ≠ 1 := Local.ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hn
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ η).IsAddHaarMeasure := (Local.ComplexCover.Construction.complex_analytic_normalization η hηc hηu hηn N).2.1
  have hm := (Local.ComplexFieldNormalization.Construction.complexField_selfDual_normalization e he hi ψ hc hu hn).2.2
  have hγ : Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 = Local.FunctionsMetaplectic.Construction.gaussianIndex ℂ η 1 := by
    rw [(Local.ComplexFieldGaussian.Construction.complexField_gaussian_normalization hArch e he hi ψ hc hu hn 1 one_ne_zero).2.2,
      (Local.ArchimedeanTestSpace.Construction.complex_gaussian_normalization η hηc hηu hηn 1 one_ne_zero).2.2]
  apply FresnelFieldTransport.LocalAnalysis.fresnel_fieldTransport e he hi N ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ) (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ η) hm _ _ f x
  intro g y
  change Local.FunctionsMetaplectic.Construction.fourierIntegral η (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ N η)
    (Local.FunctionsMetaplectic.Construction.quadraticOperator η 1 (Local.FunctionsMetaplectic.Construction.fourierIntegral η (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ N η) g.val)) y =
      Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ N * η (-Local.FunctionsMetaplectic.Construction.quadratic 1 y) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral η (Local.FunctionsMetaplectic.Construction.positionMeasure ℂ N η) (Local.FunctionsMetaplectic.Construction.quadraticOperator η (-1) g.val) y
  rw [hγ]
  exact Local.ComplexWeyl.Construction.complex_fourier_quadratic_fourier η hηc hηu hηn g y

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanFresnel.LocalAnalysis
