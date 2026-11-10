module

public import ArtinMatthews.SpectralTrueWidthKloosterman
public import ArtinMatthews.SpectralTrueWidthOrbitalScaling
public import ArtinMatthews.SpectralPositiveOrbitalKloosterman
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine positive-c orbital fibre in primitive cusp coordinates.
The raw Poincare tests retain their exact width-index multiplicity.  The
previous full identity keeps its c=0 term, central signs, and noncuspidal remainder. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0PositiveGeometricFibre_trueWidth (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N s : ℤ)*n) η hη hcη hpη) M.val) =
      ((gamma0CuspFrequencyStep N s : ℂ)*(gamma0CuspFrequencyStep N r : ℂ)) *
        (gamma0TrueWidthKloostermanSum N r s c m n *
          cuspWeylOrbitalKernel 1 m n
            (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))
            (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y))
            (gamma0TrueWidthModulus N r s c)
            (gamma0TrueWidthModulus_ne_zero N r s (by exact_mod_cast NeZero.ne c))) := by
  rw [gamma0PositiveGeometricFibre_eq_kloosterman N r s c
    ((gamma0CuspFrequencyStep N r : ℤ)*m) ((gamma0CuspFrequencyStep N s : ℤ)*n)
    ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0PeriodKloostermanSum_trueWidth,cuspWeylOrbitalKernel_trueWidth]
  ring

theorem gamma0PositiveGeometricFibre_eq_zero_of_inadmissible (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (h : ¬ (gamma0CuspFrequencyStep N r : ℤ) ∣ m ∨
      ¬ (gamma0CuspFrequencyStep N s : ℤ) ∣ n) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη) M.val) = 0 := by
  rw [gamma0PositiveGeometricFibre_eq_kloosterman N r s c m n ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0PeriodKloostermanSum_eq_zero_of_inadmissible N r s c m n h,zero_mul]

end ArtinMatthews
