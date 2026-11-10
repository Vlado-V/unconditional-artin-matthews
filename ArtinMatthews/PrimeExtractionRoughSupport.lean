module

public import ArtinMatthews.PrimeExtractionBilinearCoefficient
public import ArtinMatthews.PrimeExtractionDyadicPartition
public import ArtinMatthews.PrimeExtractionTupleBounds
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

/-! Actual support of the two extracted coefficients. Positive remaining
tuple length forces both variables above the roughness threshold. -/

namespace ArtinMatthews

open OAI.SevenEighths

theorem roughPrimeTupleCoefficient_argument_gt (a : ℕ → ℂ) {j n : ℕ} {z : ℝ}
    (hj : 0 < j) (hb : roughPrimeTupleCoefficient a j n z ≠ 0) : z < (n : ℝ) := by
  obtain ⟨hn, hrough, hlen⟩ := roughPrimeTupleCoefficient_support a j n z hb
  have hn1 : n ≠ 1 := by
    intro h
    subst n
    simp only [Nat.primeFactorsList_one, List.length_nil] at hlen
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
  exact lt_of_lt_of_le (hrough p hp hpd) (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpd))

theorem roughPrimeFirstCoefficient_support (a : ℕ → ℂ) {m : ℕ} {z : ℝ}
    (ha : roughPrimeFirstCoefficient a z m ≠ 0) : m.Prime ∧ z < (m : ℝ) := by
  classical
  by_contra h
  exact ha (by simp only [roughPrimeFirstCoefficient, ite_eq_right_iff]; exact fun hh => (h hh).elim)

theorem markedExtractionBilinearCoefficient_support {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (γ x : ℝ) {j m n : ℕ} (hj : 2 ≤ j)
    (hA : markedExtractionBilinearCoefficient e η χ G γ j x m n ≠ 0) :
    m.Prime ∧ x ^ γ < (m : ℝ) ∧ x ^ γ < (n : ℝ) := by
  unfold markedExtractionBilinearCoefficient at hA
  have hp := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hA).1).2
  have hb := (div_ne_zero_iff.mp (mul_ne_zero_iff.mp hA).2).1
  have hm := roughPrimeFirstCoefficient_support _ hp
  exact ⟨hm.1, hm.2, roughPrimeTupleCoefficient_argument_gt _ (by omega) hb⟩

/-- A nonzero term in a dyadic rectangle forces each lower endpoint to be
larger than half the actual roughness threshold. -/
theorem markedExtractionBilinearCoefficient_dyadic_lower {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (γ x : ℝ) {j m n N k l : ℕ} (hj : 2 ≤ j)
    (hm : m ∈ primeExtractionDyadicBlock N k) (hn : n ∈ primeExtractionDyadicBlock N l)
    (hA : markedExtractionBilinearCoefficient e η χ G γ j x m n ≠ 0) :
    x ^ γ / 2 < (2 : ℝ) ^ k ∧ x ^ γ / 2 < (2 : ℝ) ^ l := by
  have hs := markedExtractionBilinearCoefficient_support e η χ G γ x hj hA
  have hmhi : (m : ℝ) < 2 * (2 : ℝ) ^ k := by
    exact_mod_cast (primeExtractionDyadicBlock_bounds hm).2
  have hnhi : (n : ℝ) < 2 * (2 : ℝ) ^ l := by
    exact_mod_cast (primeExtractionDyadicBlock_bounds hn).2
  constructor <;> linarith [hs.2.1, hs.2.2]

end ArtinMatthews
