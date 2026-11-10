module

public import ArtinMatthews.MarkedMemoryPathOrphanTailData
public import ArtinMatthews.MarkedMemoryActiveChoiceBounds
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Actual path choice masses are controlled by the active occurrence
count and the sum of the literal one-line atoms. Both are computed from
the supplied finite path, rather than supplied as a factorization law. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)

theorem markedMemoryPathInactiveAtomMass_le (q : ℝ)
    (ha : ∀ j (p : P j),0 ≤ markedMemoryLineBirthAtom q n p.1) :
    markedMemoryPathInactiveAtomMass d q ≤
      ∑ j,∑ p : P j,markedMemoryLineBirthAtom q n p.1 := by
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro p _
  unfold markedMemoryPrimeInactiveAtom
  split_ifs
  · exact ha j p
  · exact le_rfl

theorem markedMemoryPathActiveChoiceAbsoluteMass_bound
    (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1)
    (ha : ∀ j (p : P j),0 ≤ markedMemoryLineBirthAtom q n p.1 ∧ markedMemoryLineBirthAtom q n p.1≤1) :
    markedMemoryPathActiveChoiceAbsoluteMass hZ d q ≤
      (((n:ℝ)+2)^2)^(Fintype.card J*((n+1)*(pads+1))) := by
  have hband (j : J) :
      (∏ p : P j,markedMemoryPrimeActiveAbsoluteMass (markedMemoryEta q n)
        (markedMemoryPathPrimeLines hZ d p) (markedMemoryPathVisits d j p)
        (markedMemoryLineBirthAtom q n p.1)) ≤
      (((n:ℝ)+2)^2)^((markedMemoryPathActivePrimes d j).card) := by
    calc
      _ ≤ ∏ p : P j,if p∈markedMemoryPathActivePrimes d j then ((n:ℝ)+2)^2 else 1 := by
        apply Finset.prod_le_prod₀
        · intro p _
          exact markedMemoryPrimeActiveAbsoluteMass_nonneg _ _ _ _
        · intro p _
          by_cases hp : p∈markedMemoryPathActivePrimes d j
          · simp only [hp,ite_true]
            exact markedMemoryPrimeActiveAbsoluteMass_bound _ _
              (markedMemoryEta_mem_unitInterval hq0 hq1 n) _ _ (ha j p).1 (ha j p).2
          · have hn : ¬(markedMemoryPathVisits d j p).Nonempty :=
              fun h => hp ((mem_markedMemoryPathActivePrimes d j p).mpr h)
            simp only [markedMemoryPrimeActiveAbsoluteMass,hn,ite_false,hp,le_refl]
      _ = _ := by
        rw [← Finset.prod_filter]
        simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.prod_const]
  calc
    _ ≤ ∏ j,(((n:ℝ)+2)^2)^((markedMemoryPathActivePrimes d j).card) :=
      Finset.prod_le_prod₀
        (fun j _ => Finset.prod_nonneg (fun p _ => markedMemoryPrimeActiveAbsoluteMass_nonneg _ _ _ _))
        (fun j _ => hband j)
    _ = (((n:ℝ)+2)^2)^(∑ j,(markedMemoryPathActivePrimes d j).card) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := by
      apply pow_le_pow_right₀
      · nlinarith [Nat.cast_nonneg n (α := ℝ)]
      · calc
          _ ≤ ∑ _j : J,(n+1)*(pads+1) :=
            Finset.sum_le_sum (fun j _ => markedMemoryPathActivePrimes_card_le d j)
          _ = _ := by simp

end
end ArtinMatthews
