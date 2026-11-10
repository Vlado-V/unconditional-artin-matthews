module

public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedAlgebra
public import ArtinMatthews.ArtinRaySmallModulus
public import ArtinMatthews.KummerCyclotomicTowerAbelian
public import ArtinMatthews.KummerCyclotomicTowerComplex
public import ArtinMatthews.KummerOriginalComplex
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ray families for both preserved Kummer towers, at the explicit
discriminant-times-relative-degree-square modulus. -/
noncomputable section
open scoped NumberField Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open GaloisIdealCharacter

theorem twelfthKummer_cyclotomic_small_ray_family
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (haq : a.natAbs ≤ q) :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr (twelfthKummerField q a)).natAbs ∣ N ∧
      Real.log (N : ℝ) ≤ (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) ∧
      ∃ ψ : (Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) →
          EvenRayCharacter (twelfthCyclotomicField q) N,
        (∀ χ, (ψ χ).idealHom =
          idealHom (twelfthCyclotomicField q) (twelfthKummerField q a) χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  refine ⟨discriminantDegreeModulus (twelfthCyclotomicField q) (twelfthKummerField q a),
    discriminantDegreeModulus_pos _ _, discr_dvd_discriminantDegreeModulus _ _,
    twelfthKummer_cyclotomic_discriminantDegreeModulus_log_le q a haq,
    discriminantDegreeRayCharacter, ?_, ?_⟩
  · intro χ
    rfl
  · exact discriminantDegreeRayCharacter_isNonprincipal

theorem twelfthKummer_original_small_ray_family
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (hq : 2 < q) (haq : a.natAbs ≤ q) :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr (twelfthKummerField q a)).natAbs ∣ N ∧
      Real.log (N : ℝ) ≤ (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) ∧
      ∃ ψ : (Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ) →
          EvenRayCharacter (primeKummerField q a) N,
        (∀ χ, (ψ χ).idealHom =
          idealHom (primeKummerField q a) (twelfthKummerField q a) χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  let := primeKummerField_isTotallyComplex q a hq
  refine ⟨discriminantDegreeModulus (primeKummerField q a) (twelfthKummerField q a),
    discriminantDegreeModulus_pos _ _, discr_dvd_discriminantDegreeModulus _ _,
    twelfthKummer_original_discriminantDegreeModulus_log_le q a haq,
    discriminantDegreeRayCharacter, ?_, ?_⟩
  · intro χ
    rfl
  · exact discriminantDegreeRayCharacter_isNonprincipal

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
