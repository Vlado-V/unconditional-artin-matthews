module

public import ArtinMatthews.SourceQuadraticDiagonalBlock
public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticPrincipalResiduePositive
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual diagonal Full residue is nonnegative and may be removed
from the upper real-part bound in the signed B3 decomposition. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticFullResidueDiagonal_nonnegative {M : ℝ} (hM : 0 < M)
    (K : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) :
    0 ≤ (sourceQuadraticZeroResidualBlock F S₀
      (sourceQuadraticDualDivisorResidue F S₀ hζ M K g) cols u g).re ∧
      (sourceQuadraticZeroResidualBlock F S₀
        (sourceQuadraticDualDivisorResidue F S₀ hζ M K g) cols u g).im = 0 := by
  rw [sourceQuadraticZeroResidualBlock_eq]
  by_cases hg : g ∈ cols
  · rw [ite_eq_left hg]
    have hu : star (u g) * u g = ((‖u g‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rfl
    rw [hu]
    obtain ⟨hr, hi⟩ := sourceQuadraticDualDivisorResidue_zero_nonnegative F S₀ hζ hM K g
    constructor
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (sq_nonneg _) hr
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hi, mul_zero, zero_mul, add_zero]
  · rw [ite_eq_right hg]
    exact ⟨le_rfl, rfl⟩

theorem sourceQuadratic_sub_fullResidueDiagonal_re_le {M : ℝ} (hM : 0 < M)
    (K : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) (z : ℂ) :
    (z - sourceQuadraticZeroResidualBlock F S₀
      (sourceQuadraticDualDivisorResidue F S₀ hζ M K g) cols u g).re ≤ z.re := by
  rw [Complex.sub_re]
  exact sub_le_self _ (sourceQuadraticFullResidueDiagonal_nonnegative F S₀ hζ hM K cols u g).1

end
end ArtinMatthews.SourceEulerAssembly
