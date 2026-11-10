module

public import ArtinMatthews.HeckePrimeNormalization
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

/-! The unrestricted literal rational-prime sum equals the finite annular
sum because the cutoff has compact positive support. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths
open scoped BigOperators Classical

def heckeRationalPrimeSmoothSum (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (H t : ℝ) : ℂ :=
  ∑' p : ℕ, if p.Prime then
    idealThetaCoeff η p*χ p*W ((p : ℝ)/H)*(p : ℂ)^((t : ℂ)*Complex.I) else 0

theorem heckeRationalPrimeSmoothSum_eq_finite (η : HeckeFamily.Character) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (a b H t : ℝ) (hH : 0 < H)
    (hsupp : Function.support W ⊆ Set.Icc a b) :
    heckeRationalPrimeSmoothSum η χ W H t =
      heckeRationalPrimeSum η χ W ⌊max 1 b*H⌋₊ H t := by
  unfold heckeRationalPrimeSmoothSum heckeRationalPrimeSum
  rw [tsum_eq_sum (s := (Finset.Icc 1 ⌊max 1 b*H⌋₊).filter Nat.Prime)]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_left (Finset.mem_filter.mp hp).2]
  · intro p hp
    by_cases hprime : p.Prime
    · rw [ite_eq_left hprime]
      have hzero : W ((p : ℝ)/H) = 0 := by
        by_contra hn
        have hs := hsupp hn
        have hpH : (p : ℝ) ≤ max 1 b*H :=
          ((div_le_iff₀ hH).mp hs.2).trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hH.le)
        exact hp (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hprime.one_lt.le, Nat.le_floor hpH⟩, hprime⟩)
      rw [hzero, mul_zero, zero_mul]
    · rw [ite_eq_right hprime]

end ArtinMatthews
