module

public import ArtinMatthews.GiantSamplingSquareRows
public import ArtinMatthews.MarkedTypeIICollisionDecay
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual squarepart rows and the supported giant primes have the
elementary counts used for the large-squarepart tail. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem giantSampling_positive_card_le (P : Finset ℕ) {Y : ℝ} (hY : 0 ≤ Y)
    (hP : ∀ p ∈ P, 0 < p ∧ (p : ℝ) ≤ Y) :
    (P.card : ℝ) ≤ Y := by
  have hsub : P ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).1, Nat.le_floor (hP p hp).2⟩
  calc
    _ ≤ ((Finset.Icc 1 ⌊Y⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (⌊Y⌋₊ : ℕ) := by simp
    _ ≤ _ := Nat.floor_le hY

theorem giantSampling_squarefreeRow_card_le (K : Finset ℕ) (B d : ℕ)
    {T : ℝ} (hT : 0 ≤ T) (hd : 0 < d) (hK : ∀ k ∈ K, (k : ℝ) ≤ 2 * T) :
    ((giantSamplingSquarefreeRow K B d).card : ℝ) ≤ 2 * T / (d : ℝ) ^ 2 := by
  apply giantSampling_positive_card_le _ (by positivity)
  intro a ha
  obtain ⟨haB, _, haK⟩ := Finset.mem_filter.mp ha
  refine ⟨(Finset.mem_Icc.mp haB).1, ?_⟩
  apply (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hd) 2)).mpr
  simpa only [Nat.cast_mul, Nat.cast_pow, mul_comm] using hK _ haK

theorem giantSampling_largeSquareRow_card_sum_le (K : Finset ℕ) (B : ℕ)
    {T D : ℝ} (hT : 0 ≤ T) (hD : 4 ≤ D) (hK : ∀ k ∈ K, (k : ℝ) ≤ 2 * T) :
    (∑ d ∈ (Finset.Icc 1 B).filter (fun d : ℕ => D < (d : ℝ)),
      ((giantSamplingSquarefreeRow K B d).card : ℝ)) ≤ 8 * T / D := by
  let P := (Finset.Icc 1 B).filter (fun d : ℕ => D < (d : ℝ))
  have hsum : (∑ d ∈ P, 1 / (d : ℝ) ^ 2) ≤ 4 / D :=
    marked_reciprocal_square_tail_le P hD (fun d hd => (Finset.mem_filter.mp hd).2.le)
  calc
    _ ≤ ∑ d ∈ P, 2 * T / (d : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      exact giantSampling_squarefreeRow_card_le K B d hT
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1 hK
    _ = (2 * T) * ∑ d ∈ P, 1 / (d : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ ≤ (2 * T) * (4 / D) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

def giantSamplingWindowBelow (x ε T : ℝ) : Finset ℕ :=
  (giantPrimeWindow x ε).filter fun ℓ => (ℓ : ℝ) ≤ 2 * x / T

theorem giantSamplingWindowBelow_card_le {x ε T : ℝ} (hx : 0 ≤ x) (hT : 0 < T) :
    ((giantSamplingWindowBelow x ε T).card : ℝ) ≤ 2 * x / T := by
  apply giantSampling_positive_card_le _ (by positivity)
  intro ℓ hℓ
  obtain ⟨hwin, hbound⟩ := Finset.mem_filter.mp hℓ
  exact ⟨((mem_giantPrimeWindow hx).mp hwin).1.pos, hbound⟩

end ArtinMatthews
