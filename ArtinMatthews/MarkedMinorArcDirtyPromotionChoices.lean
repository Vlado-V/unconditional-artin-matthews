module

public import ArtinMatthews.MarkedMinorArcDirtyPending
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual indexed promotion tuples and their literal outgoing damping.
No distinctness of numeric particles or anchors is used. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

abbrev MarkedRawPromotionTuple {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J) :=
  (j : I) → Fin (memory.1.1 j.1:ℕ)

instance markedRawPromotionTuple_fintype {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J) :
    Fintype (MarkedRawPromotionTuple memory I) := by
  classical
  unfold MarkedRawPromotionTuple
  infer_instance

def markedRawPromotionTuplePrimeProduct {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J) (t : MarkedRawPromotionTuple memory I) : ℕ :=
  ∏ j : I, ((memory.2 j.1 (t j)).1.1:ℕ)

def markedRawPromotionTupleDamping {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (ρ : ℝ) (newHits : I → ℕ)
    (t : MarkedRawPromotionTuple memory I) : ℝ := by
  classical
  exact ∏ j : I, if t j ∈ markedRawGroupHitIndices memory j.1 z hz then
    ρ^((markedRawPromotionRemainingHits memory j.1 z hz (t j)).card+newHits j) else 0

theorem markedRawPromotionTupleDamping_nonneg {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {ρ : ℝ} (hρ : 0 ≤ ρ) (newHits : I → ℕ)
    (t : MarkedRawPromotionTuple memory I) : 0 ≤ markedRawPromotionTupleDamping memory I z hz ρ newHits t := by
  classical
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · exact pow_nonneg hρ _
  · exact le_rfl

theorem markedRawPromotionTupleDamping_sum_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (newHits : I → ℕ) :
    (∑ t : MarkedRawPromotionTuple memory I, markedRawPromotionTupleDamping memory I z hz ρ newHits t) ≤
      (1/(1-ρ)^2)^(I.card) := by
  classical
  unfold markedRawPromotionTupleDamping
  rw [← Fintype.prod_sum (fun (j : I) (k : Fin (memory.1.1 j.1:ℕ)) =>
    if k ∈ markedRawGroupHitIndices memory j.1 z hz then
      ρ^((markedRawPromotionRemainingHits memory j.1 z hz k).card+newHits j) else 0)]
  calc
    _ ≤ ∏ _j : I, 1/(1-ρ)^2 := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Finset.sum_nonneg (fun k _ => by split_ifs <;> first | exact pow_nonneg hρ₀ _ | exact le_rfl)
      · intro j _
        simpa only [Finset.sum_ite_mem,Finset.univ_inter] using
          markedRawPromotion_damping_sum_le memory j.1 z hz hρ₀ hρ₁ (newHits j)
    _ = _ := by simp

/-- Imposing the actual promoted numeric product retains the same bound,
without dividing by multiplicities of repeated particles. -/
theorem markedRawPromotionTupleDamping_product_fiber_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (newHits : I → ℕ) (Z : ℕ) :
    (∑ t ∈ Finset.univ.filter (fun t : MarkedRawPromotionTuple memory I =>
        markedRawPromotionTuplePrimeProduct memory I t=Z),
      markedRawPromotionTupleDamping memory I z hz ρ newHits t) ≤ (1/(1-ρ)^2)^(I.card) := by
  classical
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun t _ _ => markedRawPromotionTupleDamping_nonneg memory I z hz hρ₀ newHits t)).trans
  exact markedRawPromotionTupleDamping_sum_le memory I z hz hρ₀ hρ₁ newHits

end ArtinMatthews
