module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.QuadraticNormIndex
public import OAI.RepresentationTheory.Weil.Local.IndexTwoPhaseCharacter
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNorm
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
public import OAI.RepresentationTheory.Weil.Local.GaussianCompact
public import OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean
public import OAI.RepresentationTheory.Weil.Local.GaussianNormInvariance


set_option backward.privateInPublic true
@[expose] public section

/-! # Gaussian Square Character -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter.Construction

noncomputable section

/-! The normalized squared actual Gaussian index is a quadratic character at a nonsplit nonarchimedean place. -/

variable {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
  [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)

def nonarchimedeanGaussianSquaredUnit (a : kˣ) : ℂˣ :=
  Units.mk0 (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2) (pow_ne_zero 2
    (FunctionsMetaplectic.Construction.phase_ne_zero (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn a.val a.ne_zero).2))

theorem nonarchimedeanGaussianSquaredUnit_norm_mul (a b : kˣ) (hb : b ∈ QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) :
    nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn (a * b) =
      nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn a := by
  apply Units.ext
  exact GaussianNormInvariance.Construction.nonarchimedean_gaussianIndex_sq_mul_norm hnd ψ hu hc hn a b hb

theorem nonarchimedeanGaussianSquaredUnit_neg (a : kˣ) :
    nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn ((-1) * a) =
      (nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn a)⁻¹ := by
  apply Units.ext
  rw [Units.val_inv_eq_inv_val]
  change FunctionsMetaplectic.Construction.gaussianIndex k ψ ((-1) * a).val ^ 2 = (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2)⁻¹
  rw [Units.val_mul]
  change FunctionsMetaplectic.Construction.gaussianIndex k ψ ((-1) * a.val) ^ 2 = _
  rw [neg_one_mul, GaussianNonarchimedean.Construction.nonarchimedean_gaussianIndex_neg hnd ψ hu hc hn a.val a.ne_zero, inv_pow]

theorem nonarchimedeanGaussianSquaredUnit_fourth (a : kˣ) :
    nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn a ^ 4 = 1 := by
  apply Units.ext
  change (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2) ^ 4 = 1
  rw [← pow_mul]
  exact GaussianNonarchimedean.Construction.nonarchimedean_gaussianIndex_eighth hnd ψ hu hc hn a.val a.ne_zero

def nonarchimedeanGaussianSquareCharacter [CompleteSpace k] (h : ¬ ∃ t : k, t ^ 2 = -1) :
    kˣ →* ℂˣ := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hnd
  exact IndexTwoPhaseCharacter.Construction.indexTwoPhaseCharacter (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) (QuadraticNormIndex.Construction.localField_quadraticNorm_index_two hnd h)
    (nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn) (-1)
    (nonarchimedeanGaussianSquaredUnit_norm_mul hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_neg hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_fourth hnd ψ hu hc hn)

theorem nonarchimedeanGaussianSquareCharacter_apply [CompleteSpace k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (a : kˣ) :
    (nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn h a).val =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 := by
  change FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ 2 = _
  rw [div_pow]

theorem nonarchimedeanGaussianSquareCharacter_square [CompleteSpace k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (a : kˣ) :
    nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn h a ^ 2 = 1 := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hnd
  exact IndexTwoPhaseCharacter.Construction.indexTwo_phase_ratio_square (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) (QuadraticNormIndex.Construction.localField_quadraticNorm_index_two hnd h)
    (nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn) (-1)
    (nonarchimedeanGaussianSquaredUnit_norm_mul hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_neg hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_fourth hnd ψ hu hc hn) a

include hnd hu hc hn in
theorem nonarchimedean_gaussianIndex_normalized_sq_mul [CompleteSpace k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (a b : kˣ) :
    (FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b).val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 *
        (FunctionsMetaplectic.Construction.gaussianIndex k ψ b.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 := by
  have hh := congrArg Units.val ((nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn h).map_mul a b)
  simpa only [Units.val_mul, nonarchimedeanGaussianSquareCharacter_apply] using hh

end

end OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter.Construction
