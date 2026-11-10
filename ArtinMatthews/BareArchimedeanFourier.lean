module

public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ComplexNormalization
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RealNormalization
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ScalarPlancherel


set_option backward.privateInPublic true
@[expose] public section

/-! # Archimedean Fourier Covers -/

namespace ArtinMatthews.QuadraticWeil.BareArchimedean

open OAI.RepresentationTheory.Weil
open OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! The exact Fourier oscillator at every archimedean completion, obtained
by transporting the reference-set normalization from its real or complex model. -/

open _root_.MeasureTheory
open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport.LocalAnalysis

local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    MeasurableSpace v.Completion := borel v.Completion
local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    BorelSpace v.Completion := ⟨rfl⟩
local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    CharZero v.Completion := ArchimedeanAdeles.Construction.completionCharZero F (.inl v)

local instance (F : Type) [Field F] [NumberField F] (v : NumberField.InfinitePlace F) :
    SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology

theorem archimedean_fourier_analysis
    (F : Type) [Field F] [NumberField F] (N : ℕ) (v : NumberField.InfinitePlace F)
    (ψ : AddChar (ArchimedeanAdeles.Construction.Completion F (.inl v)) ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    (∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N ψ) f.val ∈
        Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N) ∧
    ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inl v)) N) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N ψ)
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) N ψ) f.val) x = f.val (-x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have he : Continuous e :=
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).continuous
    have hi : Continuous e.symm :=
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
    let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
    have hc' : Continuous ψ' := hc.comp hi
    have hu' : ∀ t, ‖ψ' t‖ = 1 := fun t => hu (e.symm t)
    have hn' : ∃ t, ψ' t ≠ 1 := by
      obtain ⟨x, hx⟩ := hn
      refine ⟨e x, ?_⟩
      change ψ (e.symm (e x)) ≠ 1
      rwa [e.symm_apply_apply]
    have h := RealNormalization.LocalAnalysis.real_fourier_analysis N ψ' hc' hu' hn'
    let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ').IsAddHaarMeasure :=
      FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ' h.1
    have hm := FourierTransport.LocalAnalysis.selfDualMeasure_fieldTransport e he hi ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ')
      (fun _ hS => ScalarPlancherel.LocalAnalysis.real_scalar_indicator_plancherel ψ' hc' hu' hn' hS)
    exact FourierTransport.LocalAnalysis.fourier_fieldTransport_analysis e he hi N ψ
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) ψ) (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ') hm h.2.1 h.2.2
  · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    have he : Continuous e :=
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
    have hi : Continuous e.symm :=
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous
    let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
    have hc' : Continuous ψ' := hc.comp hi
    have hu' : ∀ t, ‖ψ' t‖ = 1 := fun t => hu (e.symm t)
    have hn' : ∃ t, ψ' t ≠ 1 := by
      obtain ⟨x, hx⟩ := hn
      refine ⟨e x, ?_⟩
      change ψ (e.symm (e x)) ≠ 1
      rwa [e.symm_apply_apply]
    have h := ComplexNormalization.LocalAnalysis.complex_fourier_analysis N ψ' hc' hu' hn'
    let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ').IsAddHaarMeasure :=
      FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ' h.1
    have hm := FourierTransport.LocalAnalysis.selfDualMeasure_fieldTransport e he hi ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ')
      (fun _ hS => ScalarPlancherel.LocalAnalysis.complex_scalar_indicator_plancherel ψ' hc' hu' hn' hS)
    exact FourierTransport.LocalAnalysis.fourier_fieldTransport_analysis e he hi N ψ
      (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F (.inl v)) ψ) (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ') hm h.2.1 h.2.2

end

end ArtinMatthews.QuadraticWeil.BareArchimedean
