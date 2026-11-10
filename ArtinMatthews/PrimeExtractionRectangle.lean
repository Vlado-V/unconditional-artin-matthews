module

public import ArtinMatthews.PrimeExtractionBilinearCoefficient
public import ArtinMatthews.PrimeExtractionDirectReduction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual smooth support removes the hyperbola cutoff before Mellin
separation. The coefficient matrix itself has no sharp product cutoff. -/

namespace ArtinMatthews

open OAI.SevenEighths
open scoped BigOperators

theorem prime_extraction_cutoff_zero_of_product_gt (Φ : ℝ → ℝ) {a T x : ℝ}
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hx : 0 < x)
    {m n : ℕ} (hmn : ⌊T * x⌋₊ < m * n) :
    Φ (((m * n : ℕ) : ℝ) / x) = 0 := by
  by_contra hne
  have hu := (hsupp hne).2
  have hl : T < (((m * n : ℕ) : ℝ) / x) :=
    (lt_div_iff₀ hx).mpr (Nat.lt_of_floor_lt hmn)
  exact (not_lt_of_ge hu) hl

theorem markedDirectTupleThetaSum_rectangle {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a T x : ℝ}
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hx : 0 < x)
    (γ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    markedDirectTupleThetaSum e η χ G Φ T γ j x =
      ∑ m ∈ Finset.Ioc 0 ⌊T * x⌋₊, ∑ n ∈ Finset.Ioc 0 ⌊T * x⌋₊,
        markedExtractionBilinearCoefficient e η χ G γ j x m n *
          (Φ (((m * n : ℕ) : ℝ) / x) : ℂ) := by
  classical
  rw [markedDirectTupleThetaSum_bilinear e η χ G Φ T γ x hj, Finset.sum_div]
  trans ∑ mn ∈ (Finset.Ioc 0 ⌊T * x⌋₊ ×ˢ Finset.Ioc 0 ⌊T * x⌋₊).filter
      (fun mn => mn.1 * mn.2 ≤ ⌊T * x⌋₊),
    markedExtractionBilinearCoefficient e η χ G γ j x mn.1 mn.2 *
      (Φ (((mn.1 * mn.2 : ℕ) : ℝ) / x) : ℂ)
  · apply Finset.sum_congr rfl
    intro mn _
    unfold markedExtractionBilinearCoefficient
    ring
  · trans ∑ mn ∈ Finset.Ioc 0 ⌊T * x⌋₊ ×ˢ Finset.Ioc 0 ⌊T * x⌋₊,
      markedExtractionBilinearCoefficient e η χ G γ j x mn.1 mn.2 *
        (Φ (((mn.1 * mn.2 : ℕ) : ℝ) / x) : ℂ)
    · apply Finset.sum_subset (Finset.filter_subset _ _)
      intro mn hmem hnot
      have hgt : ⌊T * x⌋₊ < mn.1 * mn.2 := by
        simpa only [Finset.mem_filter, hmem, true_and, not_le] using hnot
      rw [prime_extraction_cutoff_zero_of_product_gt Φ hsupp hx hgt]
      simp
    · rw [Finset.sum_product]

end ArtinMatthews
