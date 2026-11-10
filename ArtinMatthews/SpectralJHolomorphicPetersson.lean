module

public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.SpectralPeterssonGram
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The source holomorphic weight multiplies the actual normalized, true-width
Petersson term to give the odd part of the forward-J inversion. The algebra
includes weight two. The Gram theorem retains its own weight hypotheses. -/
noncomputable section
open Set Complex
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralJHolomorphicCoefficient_gram_modulus (f : ℝ → ℂ)
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (j : ℕ) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    letI : NeZero c.val := ⟨c.property.ne'⟩
    spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b a (2*j+2) m n c =
      (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)/
        (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
      spectralJOddSynthesisTerm f j
        (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ))) := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hk : 2*j+2-1 = 2*j+1 := by omega
  calc
    _ = (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)/
          (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
        (spectralJHolomorphicCoefficient f (2*j+2)*
          (2*(Real.pi : ℂ)*I^(-((2*j+2 : ℕ) : ℤ)))*
          Complex.besselJ ((2*j+1 : ℕ) : ℂ)
            (spectralPeterssonBesselArgument m n
              (gamma0TrueWidthModulus N b a (c.val : ℝ)) : ℂ)) := by
      dsimp only [gamma0PeterssonGramModulusTerm]
      rw [hk]
      ring
    _ = _ := by rw [spectralJHolomorphicCoefficient_odd_term]

theorem spectralJHolomorphicCoefficient_gram_modulus_summable (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    Summable (fun j : ℕ => ‖spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b a (2*j+2) m n c‖) := by
  simp_rw [spectralJHolomorphicCoefficient_gram_modulus,norm_mul]
  exact (spectralJOddSynthesis_summable_norm f hf hc hp _).mul_left _

theorem spectralJHolomorphicCoefficient_gram_modulus_sum (f : ℝ → ℂ)
    (N : ℕ) [NeZero N] (b a : SL(2, ℤ)) (m n : ℕ+) (c : Ioi (0 : ℕ)) :
    letI : NeZero c.val := ⟨c.property.ne'⟩
    (∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b a (2*j+2) m n c) =
      (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)/
        (gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
      spectralJOddSynthesis f
        (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ))) := by
  letI : NeZero c.val := ⟨c.property.ne'⟩
  simp_rw [spectralJHolomorphicCoefficient_gram_modulus]
  rw [tsum_mul_left]
  rfl

end ArtinMatthews
