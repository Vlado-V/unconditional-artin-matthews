module

public import ArtinMatthews.IdealGroupedFiberCount
public import ArtinMatthews.MarkedTypeIIPadCollisions
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

/-! The actual harmonic numeric-product atom, with a proved per-band
factorial bound and every original reciprocal normalizer retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]

def idealGroupedMass (P : J → Finset ℕ) (k : J → ℕ) (a : IdealGroupedLabels P k) : ℝ :=
  ∏ j, ∏ i, markedHarmonicAtom (P j) (a j i)

def idealGroupedNormalizer (P : J → Finset ℕ) (k : J → ℕ) : ℝ :=
  ∏ j, (bandReciprocalMass (P j))⁻¹ ^ (k j)

def idealGroupedProductMass (P : J → Finset ℕ) (k : J → ℕ) (n : ℕ) : ℝ :=
  ∑ a : IdealGroupedLabels P k,
    if idealGroupedProduct a = n then idealGroupedMass P k a else 0

def idealGroupedAtomBudget (P : J → Finset ℕ) (k : J → ℕ) : ℝ :=
  ∏ j, ((k j).factorial : ℝ) * (bandReciprocalMass (P j))⁻¹ ^ (k j)

omit [DecidableEq J] in
theorem idealGroupedMass_factor (P : J → Finset ℕ) (k : J → ℕ)
    (a : IdealGroupedLabels P k) :
    idealGroupedMass P k a = idealGroupedNormalizer P k / (idealGroupedProduct a : ℝ) := by
  simp only [idealGroupedMass, idealGroupedNormalizer, markedHarmonicAtom,
    div_eq_mul_inv, one_mul, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  simp only [prod_inv_distrib]
  rw [idealGroupedProduct]
  simp only [Nat.cast_prod, idealGroupProduct]
  ring

omit [DecidableEq J] in
theorem idealGroupedMass_nonneg (P : J → Finset ℕ) (k : J → ℕ)
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (a : IdealGroupedLabels P k) :
    0 ≤ idealGroupedMass P k a :=
  prod_nonneg fun j _ => prod_nonneg fun _ _ => markedHarmonicAtom_nonneg (P j) (hV j)

omit [DecidableEq J] in
theorem idealGroupedNormalizer_nonneg (P : J → Finset ℕ) (k : J → ℕ)
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) : 0 ≤ idealGroupedNormalizer P k := by
  unfold idealGroupedNormalizer
  exact prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _

theorem idealGroupedProductMass_eq (P : J → Finset ℕ) (k : J → ℕ) (n : ℕ) :
    idealGroupedProductMass P k n = (Fintype.card (IdealGroupedFiber P k n) : ℝ) *
      (idealGroupedNormalizer P k / n) := by
  unfold idealGroupedProductMass
  rw [← sum_filter]
  calc
    _ = ∑ _a ∈ (univ : Finset (IdealGroupedLabels P k)).filter (fun a => idealGroupedProduct a = n),
        idealGroupedNormalizer P k / n := by
      apply sum_congr rfl
      intro a ha
      rw [idealGroupedMass_factor, (mem_filter.mp ha).2]
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, Fintype.card_subtype]

theorem idealGroupedProductMass_le (P : J → Finset ℕ) (k : J → ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (n : ℕ) :
    idealGroupedProductMass P k n ≤ idealGroupedAtomBudget P k / n := by
  rw [idealGroupedProductMass_eq]
  calc
    _ ≤ ((∏ j, (k j).factorial : ℕ) : ℝ) * (idealGroupedNormalizer P k / n) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast idealGroupedProduct_fiber_card_le hP hdis n)
        (div_nonneg (idealGroupedNormalizer_nonneg P k hV) (Nat.cast_nonneg n))
    _ = _ := by
      simp only [Nat.cast_prod, idealGroupedNormalizer, idealGroupedAtomBudget, prod_mul_distrib]
      ring

end
end ArtinMatthews
