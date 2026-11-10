module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import OAI.RepresentationTheory.Weil.Local.Gaussian
public import OAI.RepresentationTheory.Weil.Local.GaussianCompact
public import OAI.RepresentationTheory.Weil.Local.GeneralGaussianMagnitude


set_option backward.privateInPublic true
@[expose] public section

/-! # Gaussian Square Classes -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses.Construction

noncomputable section

/-! Square-class invariance obtained from the actual damped Gaussian. -/

open _root_.MeasureTheory Filter
open scoped Classical _root_.Topology

theorem regularizedGaussian_square_mul
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (a : k) (b : kˣ) (ε : ℝ) :
    FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * b.val ^ 2) ε =
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.regularizedGaussian k ψ a (ε / ‖b.val‖ ^ 2) := by
  let F : k → ℂ := fun x => (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * ψ ((a * b.val ^ 2) * x ^ 2 / 2)
  have h := GeneralGaussianMagnitude.Construction.integral_div_unit (Measure.addHaar : Measure k) b F
  have heq : (∫ x, F (x / b.val) ∂(Measure.addHaar : Measure k)) =
      FunctionsMetaplectic.Construction.regularizedGaussian k ψ a (ε / ‖b.val‖ ^ 2) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (Real.exp (-ε * ‖x / b.val‖ ^ 2) : ℂ) * ψ ((a * b.val ^ 2) * (x / b.val) ^ 2 / 2) = _
      have hn : -ε * ‖x / b.val‖ ^ 2 = -(ε / ‖b.val‖ ^ 2) * ‖x‖ ^ 2 := by
        rw [norm_div, div_pow]
        ring
      have hq : (a * b.val ^ 2) * (x / b.val) ^ 2 / 2 = a * x ^ 2 / 2 := by
        field_simp
      rw [hn, hq]
  rw [heq] at h
  change FunctionsMetaplectic.Construction.regularizedGaussian k ψ a (ε / ‖b.val‖ ^ 2) =
      (FunctionsMetaplectic.Construction.localModulus k b : ℝ) • FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * b.val ^ 2) ε at h
  rw [h, smul_smul, inv_mul_cancel₀ (FunctionsMetaplectic.Construction.localModulus_pos k b).ne', one_smul]

theorem positive_division_tendsto_zero_right (r : ℝ) (hr : 0 < r) :
    Tendsto (fun x : ℝ => x / r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((continuous_id.div_const r).continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with x hx
    exact div_pos hx hr

theorem nonarchimedean_gaussianIntegral_square_mul
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) (b : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIntegral k ψ (a * b.val ^ 2) =
      ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.gaussianIntegral k ψ a := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  have hlim := (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn a ha).1.comp
    (positive_division_tendsto_zero_right (‖b.val‖ ^ 2) (sq_pos_of_pos (norm_pos_iff.mpr b.ne_zero)))
  have hscaled := hlim.const_smul ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ)
  have hresult : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ (a * b.val ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (((FunctionsMetaplectic.Construction.localModulus k b)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) := by
    simpa only [Function.comp_def, ← regularizedGaussian_square_mul ψ a b] using hscaled
  exact hresult.limUnder_eq

theorem nonarchimedean_gaussianIndex_square_mul
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) (b : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b.val ^ 2) = FunctionsMetaplectic.Construction.gaussianIndex k ψ a := by
  rw [FunctionsMetaplectic.Construction.gaussianIndex, nonarchimedean_gaussianIntegral_square_mul hNondiscrete ψ hu hc hn a ha b,
    Complex.real_smul, Gaussian.Construction.phase_positive_mul ((FunctionsMetaplectic.Construction.localModulus k b)⁻¹) (inv_pos.mpr (FunctionsMetaplectic.Construction.localModulus_pos k b))]
  rfl

end

end OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses.Construction
