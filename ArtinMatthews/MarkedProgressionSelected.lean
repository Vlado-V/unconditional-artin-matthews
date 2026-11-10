module

public import ArtinMatthews.MarkedProgressionIndexed
public import ArtinMatthews.MarkedProgressionTruncation
public import ArtinMatthews.MarkedProgressionExpansion
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

/-! Selected residual tails, their exact squarefree divisors, and their
factorial-decaying reciprocal model mass. -/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

noncomputable def markedSelectedHomogeneous (P S : Finset ℕ) (k : ℕ) (θ : ℝ) (u : ℕ) : ℝ :=
  markedIndexedDivisorPolynomial ((P \ S).powersetCard k)
    (fun T => ∏ p ∈ S ∪ T, p) (fun _ => θ ^ k) u

/-- The positive omitted tail retains the represented union exactly. -/
theorem marked_selected_tail_eq (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) (u a k : ℕ) (ρ : ℝ) :
    (if S ⊆ activeDivisors P u then markedResidualTail k P S u a ρ else 0) =
      markedSelectedHomogeneous P S k (1 - ρ ^ a) u := by
  classical
  unfold markedResidualTail BonferroniDensity.elementarySum markedSelectedHomogeneous
    markedIndexedDivisorPolynomial
  have hif : (if S ⊆ activeDivisors P u then
      ∑ T ∈ (P \ S).powersetCard k, ∏ p ∈ T, markedResidualInput u a ρ p else 0) =
      ∑ T ∈ (P \ S).powersetCard k, if S ⊆ activeDivisors P u then
        ∏ p ∈ T, markedResidualInput u a ρ p else 0 := by
    by_cases hs : S ⊆ activeDivisors P u <;> simp [hs]
  rw [hif]
  apply Finset.sum_congr rfl
  intro T hT
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
  simpa only [markedResidualInput, hcard] using marked_selected_hit_product P S T hP hS
    (fun _ hp => (Finset.mem_sdiff.mp (hsub hp)).1) u (1 - ρ ^ a)

/-- Exact truncated selected residual, before the scalar represented damping. -/
theorem marked_selected_truncation_eq (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : S ⊆ P) (u a k : ℕ) (ρ : ℝ) :
    (if S ⊆ activeDivisors P u then markedResidualTruncation k P S u a ρ else 0) =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j *
        markedSelectedHomogeneous P S j (1 - ρ ^ a) u := by
  classical
  unfold markedResidualTruncation BonferroniDensity.densityPolynomial
  calc
    _ = ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j *
        (if S ⊆ activeDivisors P u then markedResidualTail j P S u a ρ else 0) := by
      by_cases hs : S ⊆ activeDivisors P u <;> simp [hs, markedResidualTail]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [marked_selected_tail_eq P S hP hS]

/-- Reciprocal mass separates the represented divisor and omitted primes. -/
theorem marked_selected_reciprocal_mass (P S : Finset ℕ) (k : ℕ) (θ : ℝ) :
    (∑ T ∈ (P \ S).powersetCard k, θ ^ k / (∏ p ∈ S ∪ T, p : ℕ)) =
      (1 / (∏ p ∈ S, p : ℕ)) *
        BonferroniDensity.elementarySum (P \ S) (fun p => θ / (p : ℝ)) k := by
  classical
  unfold BonferroniDensity.elementarySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hp hpT
    exact (Finset.mem_sdiff.mp (hsub hpT)).2 hp
  rw [Finset.prod_union hdis, Nat.cast_mul, Finset.prod_div_distrib]
  simp only [Finset.prod_const, hcard]
  simp only [Nat.cast_prod]
  ring

/-- The selected positive tail has factorial decay with its actual
represented-divisor reciprocal factor retained. -/
theorem marked_selected_reciprocal_mass_le (P S : Finset ℕ) (a k : ℕ)
    {ρ V : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, (1 - ρ ^ a) / (p : ℝ) ≤ V) :
    (∑ T ∈ (P \ S).powersetCard k,
      (1 - ρ ^ a) ^ k / (∏ p ∈ S ∪ T, p : ℕ)) ≤
      (1 / (∏ p ∈ S, p : ℕ)) * (V ^ k / k.factorial) := by
  rw [marked_selected_reciprocal_mass]
  exact mul_le_mul_of_nonneg_left (markedResidual_model_tail_le P S a k hρ0 hρ1 hV hmass)
    (by positivity)

end ArtinMatthews
