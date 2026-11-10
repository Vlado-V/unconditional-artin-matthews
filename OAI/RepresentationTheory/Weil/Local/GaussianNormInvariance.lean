module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup
public import OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic
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
public import OAI.RepresentationTheory.Weil.Local.FresnelChangeCoordinates
public import OAI.RepresentationTheory.Weil.Local.Gaussian
public import OAI.RepresentationTheory.Weil.Local.GaussianCompact
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormReflection


set_option backward.privateInPublic true
@[expose] public section

/-! # Gaussian Norm Invariance -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianNormInvariance.Construction

noncomputable section

/-! Squared actual Gaussian indices are invariant under multiplication by a quadratic norm. -/

open _root_.Matrix

theorem phase_diagonalGaussianCoefficient_pair
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (a : kˣ) (ha : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val ≠ 0) :
    FunctionsMetaplectic.Construction.phase (DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ (fun _ : Fin 2 => a)) = FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 := by
  have he : DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ (fun _ : Fin 2 => a) =
      Complex.ofReal (((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k a))⁻¹) ^ 2) * FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 := by
    simp only [DiagonalQuadratic.Construction.diagonalGaussianCoefficient, Fin.prod_univ_two]
    push_cast
    ring
  rw [he, Gaussian.Construction.phase_positive_mul _ (sq_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (FunctionsMetaplectic.Construction.localModulus_pos k a))))]
  rw [FunctionsMetaplectic.Construction.phase, norm_pow, FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ a.val ha, one_pow, Complex.ofReal_one, div_one]

theorem nonarchimedean_gaussianIndex_sq_mul_norm
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (hn : ∃ t : k, ψ t ≠ 1) (a b : kˣ) (hb : b ∈ QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b).val ^ 2 = FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 := by
  obtain ⟨s, t, hst⟩ := hb
  have hN : s ^ 2 + t ^ 2 ≠ 0 := by rw [hst]; exact b.ne_zero
  let A := QuadraticNormReflection.Construction.quadraticNormGeneralLinear s t hN
  have hdiv : (a * b).val / (s ^ 2 + t ^ 2) = a.val := by
    rw [hst, Units.val_mul]
    field_simp
  have hinv : (a * b).val⁻¹ * (s ^ 2 + t ^ 2) = a.val⁻¹ := by
    rw [hst, Units.val_mul]
    field_simp
  have hq (x : FunctionsMetaplectic.Construction.Position k 2) :
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val) (A⁻¹.val *ᵥ x) =
        FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => a.val) x := by
    change FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val)
      ((QuadraticNormReflection.Construction.quadraticNormGeneralLinear s t hN)⁻¹.val *ᵥ x) = _
    rw [QuadraticNormReflection.Construction.quadratic_normGeneralLinear_inverse, hdiv]
  have hqi (x : FunctionsMetaplectic.Construction.Position k 2) :
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val⁻¹) (A.val *ᵥ x) =
        FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => a.val⁻¹) x := by
    change FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val⁻¹)
      (QuadraticNormReflection.Construction.quadraticNormReflection s t *ᵥ x) = _
    rw [QuadraticNormReflection.Construction.quadratic_normReflection, hinv]
  have hcoef := FresnelChangeCoordinates.Construction.nonarchimedean_diagonalGaussianCoefficient_congruence hnd ψ hu hc hn
    (fun _ : Fin 2 => a * b) (fun _ : Fin 2 => a) A (QuadraticNormReflection.Construction.quadraticNormReflection_isSymm s t) hq hqi
  have ha0 := (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn a.val a.ne_zero).2
  have hab0 := (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn (a * b).val (a * b).ne_zero).2
  have hp := congrArg FunctionsMetaplectic.Construction.phase hcoef
  rw [phase_diagonalGaussianCoefficient_pair ψ a ha0,
    Gaussian.Construction.phase_positive_mul _ (FunctionsMetaplectic.Construction.localModulus_pos k _), phase_diagonalGaussianCoefficient_pair ψ (a * b) hab0] at hp
  exact hp.symm

end

end OAI.RepresentationTheory.Weil.Local.GaussianNormInvariance.Construction
