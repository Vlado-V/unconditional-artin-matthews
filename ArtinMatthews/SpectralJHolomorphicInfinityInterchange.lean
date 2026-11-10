module

public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.SpectralPeterssonGram
public import ArtinMatthews.SpectralJHolomorphicInfinitySum
public import ArtinMatthews.SpectralJHolomorphicPetersson
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence justifies the actual odd-weight/modulus interchange,
retaining the source Kloosterman order and true-width scaling. -/
noncomputable section
open Set Complex
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralJHolomorphicCoefficient_leftInfinity_interchange
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (N : ℕ) [NeZero N]
    (b : SL(2, ℤ)) (m n : ℕ+) :
    (∑' j : ℕ, ∑' c : Ioi (0 : ℕ), spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b 1 (2*j+2) m n c) =
      ∑' c : Ioi (0 : ℕ),
        letI : NeZero c.val := ⟨c.property.ne'⟩
        (gamma0TrueWidthKloostermanSum N b 1 c.val (n : ℤ) (m : ℤ)/
          (gamma0TrueWidthModulus N b 1 (c.val : ℝ) : ℂ))*
          spectralJOddSynthesis f (spectralPeterssonBesselArgument m n
            (gamma0TrueWidthModulus N b 1 (c.val : ℝ))) := by
  have hs := (spectralJHolomorphicCoefficient_leftInfinity_summable_norm f hf hc hp N b m n).of_norm
  calc
    _ = ∑' c : Ioi (0 : ℕ), ∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        gamma0PeterssonGramModulusTerm N b 1 (2*j+2) m n c := hs.tsum_comm.symm
    _ = _ := tsum_congr fun c => spectralJHolomorphicCoefficient_gram_modulus_sum f N b 1 m n c

end ArtinMatthews
