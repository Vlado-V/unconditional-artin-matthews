module

public import ArtinMatthews.CubicThetaShiftedCorrelation
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

/-! The literal source correlation estimate consumed by the final
bilinear arithmetic. Its two common-prime-part factors remain explicit. -/

noncomputable section
namespace ArtinMatthews
open Set OAI OAI.SevenEighths
open scoped ContDiff

def ShiftedABLCorrelationBound (N : ℕ) (η : HeckeFamily.Character)
    (ν : ℝ) (Cg : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ m1 m2 : ℕ, m1 ≠ m2 → Squarefree m1 → Squarefree m2 → N.Coprime (m1*m2) →
    ∀ M T : ℝ, 1 ≤ M → 1 ≤ T →
      M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
      ∀ (g : ℝ → ℂ), ContDiff ℝ ∞ g → Function.support g ⊆ Icc T (2*T) →
        (∀ j x, ‖iteratedDeriv j g x‖ ≤ Cg j/T^j) →
        ‖thetaShiftedCorrelation η m1 m2 g‖ ≤ C*(M*T)^ν*
          (Real.sqrt (M*T+1)*Real.sqrt M*(shiftedCommonPrimePart m1 m2 : ℝ)/
            Real.sqrt (m1.gcd m2) +
            (M*T+1)^(3/4 : ℝ)*(shiftedCommonPrimePart m1 m2 : ℝ)^(1/4 : ℝ)/M^(1/4 : ℝ))

def ShiftedABLCorrelationSource (N : ℕ) (η : HeckeFamily.Character) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ Cg : ℕ → ℝ, (∀ j, 0 ≤ Cg j) →
    ∃ C : ℝ, 0 < C ∧ ShiftedABLCorrelationBound N η ν Cg C

end ArtinMatthews
