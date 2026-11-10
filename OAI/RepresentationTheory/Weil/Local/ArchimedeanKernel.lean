module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FieldFourier
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
public import OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification
public import OAI.RepresentationTheory.Weil.Local.ComplexBareKernel
public import OAI.RepresentationTheory.Weil.Local.FieldOscillator
public import OAI.RepresentationTheory.Weil.Local.RealBareKernel


set_option backward.privateInPublic true
@[expose] public section

/-! # Archimedean Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel.Construction

noncomputable section

/-! Bare-kernel signs for every archimedean field presentation, independently of its chosen norm. -/

theorem fieldCharacter_continuous {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he' : Continuous e.symm) (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) :
    Continuous (fun t => FieldFourier.Construction.fieldCharacter e ψ t) := hc.comp he'

theorem fieldCharacter_unitary {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) :
    ∀ t, ‖FieldFourier.Construction.fieldCharacter e ψ t‖ = 1 := fun t => hu (e.symm t)

theorem fieldCharacter_nontrivial {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) (ψ : AddChar k ℂ) (hn : ∃ t, ψ t ≠ 1) :
    ∃ t, FieldFourier.Construction.fieldCharacter e ψ t ≠ 1 := by
  obtain ⟨t, ht⟩ := hn
  refine ⟨e t, ?_⟩
  change ψ (e.symm (e t)) ≠ 1
  rwa [e.symm_apply_apply]

theorem archimedean_metaplectic_kernel_sign
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1) {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) (ha : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.val.2 f = ε • f := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  rcases ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, he'⟩ | ⟨e, he, he'⟩
  · let b := FieldOscillator.Construction.fieldMetaplecticTransport e he he' n ψ a
    have hb : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (FieldFourier.Construction.fieldCharacter e ψ) b = 1 := by
      change OscillatorProjection.Construction.oscillatorProjection ℝ n (FieldFourier.Construction.fieldCharacter e ψ) (FieldOscillator.Construction.fieldOscillatorTransport e he he' n ψ a.val) = 1
      rw [FieldOscillator.Construction.fieldOscillatorTransport_projection]
      change FieldFourier.Construction.fieldSymplecticMap e n (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a) = 1
      rw [ha, map_one]
    obtain ⟨ε, hε, hs⟩ := RealBareKernel.Construction.real_metaplectic_kernel_sign (FieldFourier.Construction.fieldCharacter e ψ)
      (fieldCharacter_continuous e he' ψ hc) (fieldCharacter_unitary e ψ hu)
      (fieldCharacter_nontrivial e ψ hn) b hb
    exact ⟨ε, hε, FieldOscillator.Construction.fieldMetaplecticTransport_scalar_pullback e he he' n ψ a ε hs⟩
  · let b := FieldOscillator.Construction.fieldMetaplecticTransport e he he' n ψ a
    have hb : FunctionsMetaplectic.Construction.metaplecticProjection ℂ n (FieldFourier.Construction.fieldCharacter e ψ) b = 1 := by
      change OscillatorProjection.Construction.oscillatorProjection ℂ n (FieldFourier.Construction.fieldCharacter e ψ) (FieldOscillator.Construction.fieldOscillatorTransport e he he' n ψ a.val) = 1
      rw [FieldOscillator.Construction.fieldOscillatorTransport_projection]
      change FieldFourier.Construction.fieldSymplecticMap e n (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a) = 1
      rw [ha, map_one]
    obtain ⟨ε, hε, hs⟩ := ComplexBareKernel.Construction.complex_metaplectic_kernel_sign (FieldFourier.Construction.fieldCharacter e ψ)
      (fieldCharacter_continuous e he' ψ hc) (fieldCharacter_unitary e ψ hu)
      (fieldCharacter_nontrivial e ψ hn) b hb
    exact ⟨ε, hε, FieldOscillator.Construction.fieldMetaplecticTransport_scalar_pullback e he he' n ψ a ε hs⟩

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel.Construction
