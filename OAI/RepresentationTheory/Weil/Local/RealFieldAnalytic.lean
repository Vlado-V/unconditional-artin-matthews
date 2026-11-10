module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.RepresentationTheory.Weil.Local.RealFieldEq
public import OAI.RepresentationTheory.Weil.Local.RealNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! # Real Field Analytic -/

namespace OAI.RepresentationTheory.Weil.Local.RealFieldAnalytic.Construction

noncomputable section

/-! All analytic clauses of LocalWeil for an arbitrary real topological field presentation. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem realField_fourier_inversion
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (n : ℕ) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val) x = f.val (-x) := by
  let η := FieldFourier.Construction.fieldCharacter e ψ
  have hηc : Continuous (fun t => η t) := hc.comp he'
  have hηu : ∀ t, ‖η t‖ = 1 := fun t => hu (e.symm t)
  have hηn : ∃ t, η t ≠ 1 := by
    obtain ⟨t, ht⟩ := hn
    refine ⟨e t, ?_⟩
    change ψ (e.symm (e t)) ≠ 1
    rwa [e.symm_apply_apply]
  have ha := RealNormalization.Construction.real_analytic_normalization η hηc hηu hηn n
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℝ η).IsAddHaarMeasure := ha.2.1
  have hmap := (RealFieldEq.Construction.realField_selfDual_normalization e he he' ψ hc hu hn).2.2
  have hF (g : FunctionsMetaplectic.Construction.Position k n → ℂ) (y : FunctionsMetaplectic.Construction.Position ℝ n) :
      FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℝ n η) (fun z => g (fun i => e.symm (z i))) y =
        FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) g (fun i => e.symm (y i)) :=
    FieldFourier.Construction.field_fourierIntegral e he he' (FunctionsMetaplectic.Construction.selfDualMeasure k ψ) (FunctionsMetaplectic.Construction.selfDualMeasure ℝ η) hmap n ψ g y
  have hinner : FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℝ n η)
      (fun y => f.val (fun i => e.symm (y i))) =
    fun y => FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val (fun i => e.symm (y i)) :=
      funext (hF f.val)
  let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
  have hh := ha.2.2.2 (C f) (fun i => e (x i))
  change FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℝ n η)
      (FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℝ n η) (fun y => f.val (fun i => e.symm (y i))))
      (fun i => e (x i)) = f.val (fun i => e.symm (-e (x i))) at hh
  rw [hinner, hF] at hh
  simpa only [RingEquiv.symm_apply_apply, map_neg] using! hh

theorem realField_analytic_normalization
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℝ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (n : ℕ) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure ∧
    (∀ a : k, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1) ∧
    (∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val) x = f.val (-x)) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  have hμ := RealFieldEq.Construction.realField_selfDual_normalization e he he' ψ hc hu hn
  exact ⟨hμ.1, hμ.2.1,
    fun a ha => (RealFieldEq.Construction.realField_gaussian_normalization hArch e he he' ψ hc hu hn a ha).1,
    realField_fourier_inversion e he he' ψ hc hu hn n⟩

end

end OAI.RepresentationTheory.Weil.Local.RealFieldAnalytic.Construction
