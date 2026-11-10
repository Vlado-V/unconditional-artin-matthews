module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.ComplexPowerGaussian
public import OAI.RepresentationTheory.Weil.Local.FieldFourier
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
public import OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel
public import OAI.RepresentationTheory.Weil.Local.ComplexTransportedNorm


set_option backward.privateInPublic true
@[expose] public section

/-! # Complex Field Gaussian -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFieldGaussian.Construction

noncomputable section

/-! Actual Gaussian normalization in every complex topological field presentation. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

theorem regularizedGaussian_complexField_power
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (p : ℝ) (hNorm : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖ ^ p) (a : k) (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian k ψ a ε = (FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℂ) *
      ComplexPowerGaussian.Construction.complexRegularizedPowerGaussian p (FieldFourier.Construction.fieldCharacter e ψ) (e a) ε := by
  rw [FunctionsMetaplectic.Construction.regularizedGaussian, FieldCoordinates.Construction.fieldReferenceHaar_integral e he he']
  change (FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℂ) *
    (∫ z, (Real.exp (-ε * ‖e.symm z‖ ^ 2) : ℂ) * ψ (a * e.symm z ^ 2 / 2) ∂Measure.addHaar) = _
  congr 1
  unfold ComplexPowerGaussian.Construction.complexRegularizedPowerGaussian
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    have hn : (‖z‖ ^ p) ^ (2 : ℕ) = ‖z‖ ^ (2 * p) := by
      rw [mul_comm (2 : ℝ) p, Real.rpow_mul (norm_nonneg z), Real.rpow_two]
    rw [hNorm z, hn]
    congr 1
    change ψ (a * e.symm z ^ 2 / 2) = ψ (e.symm (e a * z ^ 2 / 2))
    congr 1
    rw [map_div₀, map_mul, map_pow, map_ofNat, RingEquiv.symm_apply_apply]

theorem complexField_gaussian_limit_positive [CompleteSpace k] [CharZero k]
    (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (a : k) (ha : a ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (r : ℂ)) := by
  obtain ⟨p, hp, hp1, hNorm⟩ := ComplexTransportedNorm.Construction.continuous_complex_embedding_norm_power hArch e.symm.toRingHom he'
  obtain ⟨r, hr, ht⟩ := ComplexPowerGaussian.Construction.complex_power_gaussian_limit_positive p hp hp1 (FieldFourier.Construction.fieldCharacter e ψ)
    (ArchimedeanKernel.Construction.fieldCharacter_continuous e he' ψ hc) (ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hu)
    (ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hn) (e a) ((map_ne_zero e).mpr ha)
  refine ⟨(FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℝ) * r,
    mul_pos (FieldCoordinates.Construction.fieldReferenceHaarFactor_pos e he he') hr, ?_⟩
  have h := ht.const_mul (FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' : ℂ)
  rw [Complex.ofReal_mul]
  exact h.congr fun ε => (regularizedGaussian_complexField_power e he he' ψ p hNorm a ε).symm

theorem complexField_gaussian_normalization [CompleteSpace k] [CharZero k]
    (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (a : k) (ha : a ≠ 0) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a = 1 := by
  obtain ⟨r, hr, ht⟩ := complexField_gaussian_limit_positive hArch e he he' ψ hc hu hn a ha
  have hI : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a = (r : ℂ) := ht.limUnder_eq
  refine ⟨by rwa [hI], ?_, ?_⟩
  · rw [hI]
    exact Complex.ofReal_ne_zero.mpr hr.ne'
  · rw [FunctionsMetaplectic.Construction.gaussianIndex, hI]
    exact Gaussian.Construction.phase_positive_real r hr

end

end OAI.RepresentationTheory.Weil.Local.ComplexFieldGaussian.Construction
