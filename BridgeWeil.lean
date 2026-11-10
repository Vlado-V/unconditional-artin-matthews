module

public import ArtinMatthews.KloostermanFourthMoment
public import rml.weil.crt_and_completion
public import ArtinMatthews.KloostermanWeakBound
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
public import rml.weil.contracts
public import rml.weil.prime_kloosterman


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reuse of Charlie Dorsey's Weil Bounds Toolkit at commit
0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68 (Apache-2.0).
The finite sum is identified before any estimate is transferred. -/

namespace ArtinMatthews

open scoped BigOperators

theorem unitKloostermanSum_eq_weilToolkit (N : ℕ) [NeZero N]
    (h k : ZMod N) :
    unitKloostermanSum N h k = RML.ExpSum.Weil.kloostermanUnitSum N k h := by
  classical
  unfold unitKloostermanSum doubleCharacterSum RML.ExpSum.Weil.kloostermanUnitSum
  apply Finset.sum_congr rfl
  intro u _
  rw [zmodAddEquiv_apply_eq_stdAddChar, zmodAddEquiv_apply_eq_stdAddChar,
    ← AddChar.map_add_eq_mul]

theorem unitKloostermanSum_prime_weil_bound (p : ℕ) [Fact p.Prime]
    (h k : ZMod p) (hnot : h ≠ 0 ∨ k ≠ 0) :
    ‖unitKloostermanSum p h k‖ ≤ 2 * Real.sqrt p := by
  rw [unitKloostermanSum_eq_weilToolkit]
  exact RML.ExpSum.Weil.kloostermanUnitSum_prime_le_two_sqrt_of_not_both_zero
    RML.ExpSum.Weil.prime_bound p k h hnot.symm

theorem unitKloostermanSum_squarefree_weil_bound_right
    {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (h k : ZMod q) (hk : IsUnit k) :
    ‖unitKloostermanSum q h k‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * Real.sqrt q := by
  rw [unitKloostermanSum_eq_weilToolkit]
  exact RML.ExpSum.Weil.squarefreeUnitNumerator_bound hsq k h hk

end ArtinMatthews
