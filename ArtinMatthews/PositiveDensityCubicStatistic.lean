module

public import ArtinMatthews.PositiveDensityCubicRamification
public import ArtinMatthews.PositiveDensityCandidateCRT
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

/-! The selected statistic on the actual split progression uses precisely
the unramified Frobenius gate. The comparison retains the shifted weight,
the unit-class restriction and the giant-prime divisor count. -/

noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem giantSelectedPrimeTest_cubic_frobenius_eventually {S : Finset ℤ}
    (hS : AdmissibleBases S) {u : ℕ} (hprog : IsQuadraticProgressionFor S u 1)
    (Y : ℕ) (ε : ℝ) (Φ : ℝ → ℝ) (hΦ : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1)
    {T : ℝ} (hT₁ : 1 < T) (hT₂ : T < 2) (hs : Function.support Φ ⊆ Set.Ioo 1 T) :
    let U := giantSieveEnlargedUnits hprog Y
    ∀ᶠ x : ℝ in atTop,
      giantSelectedPrimeTest U (giantCubicSieveSelection S (giantCubicRamifiedPrimes S)) ε Φ T x =
        giantSelectedPrimeTest U (giantCubicFrobeniusSelection S) ε Φ T x := by
  classical
  let U := giantSieveEnlargedUnits hprog Y
  filter_upwards [giantSieveCandidates_structural_eventually hS U (fun _ => True) ε Φ
    hΦ hT₁ hT₂ hs] with x hx
  unfold giantSelectedPrimeTest
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hU : ∃ v ∈ U, (v : ZMod
      (enlargedModulus (quadraticModulus S) (giantSieveNewPrimes S Y))) = p
  · by_cases hw : giantSieveWeight Φ x p = 0
    · simp only [hw, Complex.ofReal_zero, zero_mul, ite_self]
    · by_cases hg : (giantPrimeFactors (p - 1) x ε).Nonempty
      · have hpU : p ∈ giantSieveCandidates U (fun _ => True) ε Φ T x :=
          mem_giantSieveCandidates.mpr ⟨hp, hU, trivial, hw, hg⟩
        have hp' := hx p hpU
        have hp₃ := (giantSieve_enlarged_prime_conditions hprog hp'.1 hU).2.1
        rw [giantCubicFrobeniusSelection_iff hp'.1 hp₃ hp'.2.2.1]
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hg, Finset.card_empty,
          Nat.cast_zero, Complex.ofReal_zero, mul_zero, ite_self]
  · have hz : giantUnitResidueIndicator (giantSieveEnlargedUnits hprog Y) p = 0 := by
      unfold giantUnitResidueIndicator
      exact ite_eq_right (fun h => hU (Finset.mem_image.mp h))
    simp only [hz, mul_zero, zero_mul, ite_self]

end ArtinMatthews
