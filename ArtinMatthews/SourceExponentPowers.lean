module

public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourcePrimeExponentProducts
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Literal powers of the fixed allowed prime-generator products. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourcePrimeExponentNorm_nsmul (e : SourcePrimeExponents F S₀) (k : ℕ) :
    sourcePrimeExponentNorm F S₀ (k • e) = sourcePrimeExponentNorm F S₀ e ^ k := by
  induction k with
  | zero => rw [zero_nsmul, sourcePrimeExponentNorm_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, sourcePrimeExponentNorm_add, ih, pow_succ]

theorem sourcePrimeExponentIdeal_nsmul (e : SourcePrimeExponents F S₀) (k : ℕ) :
    sourcePrimeExponentIdeal F S₀ (k • e) = sourcePrimeExponentIdeal F S₀ e ^ k := by
  induction k with
  | zero => rw [zero_nsmul, sourcePrimeExponentIdeal_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, sourcePrimeExponentIdeal_add, ih, pow_succ]

theorem sourcePrimeExponentGenerator_nsmul {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (e : SourcePrimeExponents F S₀) (k : ℕ) :
    sourcePrimeExponentGenerator F hζ S₀ (k • e) = sourcePrimeExponentGenerator F hζ S₀ e ^ k := by
  induction k with
  | zero => rw [zero_nsmul, sourcePrimeExponentGenerator_zero, pow_zero]
  | succ k ih => rw [succ_nsmul, sourcePrimeExponentGenerator_add, ih, pow_succ]

theorem sourcePrimeExponentNorm_squarefree_cube (c n : SourcePrimeExponents F S₀) :
    sourcePrimeExponentNorm F S₀ (c + 3 • n) =
      sourcePrimeExponentNorm F S₀ c * sourcePrimeExponentNorm F S₀ n ^ 3 := by
  rw [sourcePrimeExponentNorm_add, sourcePrimeExponentNorm_nsmul]

end
end ArtinMatthews
