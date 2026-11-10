module

public import ArtinMatthews.PrimeExtractionCompositeCoefficient
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed Dirichlet character belongs to the whole integer during
ordinary prime extraction. Every ordered factorization and its original
factorial mass are retained, including repeated prime factors. -/
namespace ArtinMatthews
open scoped BigOperators

theorem giant_character_list_product {M : ℕ} (χ : DirichletCharacter ℂ M)
    (a : ℕ → ℂ) (l : List ℕ) :
    (l.map (fun p => a p * χ p)).prod = χ l.prod * (l.map a).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, ih, Nat.cast_mul, map_mul]
    ring

/-- Twisting every prime factor is exactly twisting the original integer,
with no squarefreeness or coprimality assumption. -/
theorem giant_character_ordered_tuple {M : ℕ} (χ : DirichletCharacter ℂ M)
    (a : ℕ → ℂ) (j n : ℕ) (z : ℝ) :
    roughPrimeTupleCoefficient (fun p => a p * χ p) j n z =
      χ n * roughPrimeTupleCoefficient a j n z := by
  unfold roughPrimeTupleCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [giant_character_list_product,
    ((mem_roughOrderedPrimeFactorizations j n z l).mp hl).2.1]

/-- All original ordered-factorization factorial denominators survive the
fixed-character extraction. -/
theorem giant_character_composite_coefficient {M : ℕ} (χ : DirichletCharacter ℂ M)
    (a : ℕ → ℂ) (J n : ℕ) (z : ℝ) :
    roughCompositeCoefficient (fun p => a p * χ p) J n z =
      χ n * roughCompositeCoefficient a J n z := by
  unfold roughCompositeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [giant_character_ordered_tuple]
  ring

theorem giant_character_ordered_tuple_norm_le {M : ℕ} (χ : DirichletCharacter ℂ M)
    (a : ℕ → ℂ) (j n : ℕ) (z : ℝ) :
    ‖roughPrimeTupleCoefficient (fun p => a p * χ p) j n z‖ ≤
      ‖roughPrimeTupleCoefficient a j n z‖ := by
  rw [giant_character_ordered_tuple, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

end ArtinMatthews
