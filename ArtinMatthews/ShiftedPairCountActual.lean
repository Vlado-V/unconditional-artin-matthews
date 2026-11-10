module

public import ArtinMatthews.ShiftedPairCountDivisible
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Specialization of the spacing count to the literal gcd and common
prime part of the pair of source integers. -/
namespace ArtinMatthews

def shiftedActualPairs (B d D : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
    (fun p => p.1≠p.2 ∧ p.1.gcd p.2=d ∧ shiftedCommonPrimePart p.1 p.2=D)

theorem shiftedActualPairs_subset (B d D : ℕ) :
    shiftedActualPairs B d D ⊆ shiftedDivisiblePairs B d D := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hm,hne,hgcd,hpart⟩
  apply Finset.mem_filter.mpr
  refine ⟨hm,hne,?_,?_,?_⟩
  · rw [← hgcd]
    exact Nat.gcd_dvd_left _ _
  · rw [← hgcd]
    exact Nat.gcd_dvd_right _ _
  · have hdiv : D ∣ ((p.1 : ℤ)-p.2).natAbs := by
      rw [← hpart]
      exact commonPrimePart_dvd _ _
    have hz : (D : ℤ) ∣ (p.1 : ℤ)-p.2 := by
      rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast]
      exact hdiv
    apply Nat.modEq_iff_dvd.mpr
    simpa only [neg_sub] using dvd_neg.mpr hz

/-- Literal fixed-(d,D) off-diagonal count, stronger than the estimate
restricted to squarefree pairs used in §5.3. -/
theorem shiftedActualPairs_card_real (B d D : ℕ)
    (hd : 0<d) (hD : 0<D) (hdD : d∣D) :
    ((shiftedActualPairs B d D).card : ℝ) ≤ 2*(B : ℝ)^2/((d : ℝ)*(D : ℝ)) := by
  have hc : ((shiftedActualPairs B d D).card : ℝ) ≤
      ((shiftedDivisiblePairs B d D).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (shiftedActualPairs_subset B d D)
  exact hc.trans (shiftedDivisiblePairs_card_real B d D hd hD hdD)

end ArtinMatthews
