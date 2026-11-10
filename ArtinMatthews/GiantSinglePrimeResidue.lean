module

public import ArtinMatthews.MarkedTypeIIMemory
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Literal single-prime residue expectations

The residue convention is `r + h i = 0`. The reciprocal residue cardinality
is exactly `1 / p`. The visit weights may be arbitrary real numbers.
-/

namespace ArtinMatthews

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal hit indicator at the translated residue. -/
def giantSignedPrimeResidueHit (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (i : Fin n) (r : ZMod p) : ℝ :=
  if r + (h i : ZMod p) = 0 then 1 else 0

/-- Equality of two visit offsets modulo the prime. -/
def giantSignedPrimeOffsetHit (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (i a : Fin n) : ℝ :=
  if (h i : ZMod p) = (h a : ZMod p) then 1 else 0

/-- The damping at an unmarked visit, relative to an anchor visit. -/
def giantSignedPrimeDamping (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (i a : Fin n) : ℝ :=
  1 - (1 - q i) * giantSignedPrimeOffsetHit p h i a

/-- Compatibility of every active offset with the selected anchor. -/
def GiantSignedPrimeActiveCompatible (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (A : Finset (Fin n)) (a : Fin n) : Prop :=
  ∀ i ∈ A, (h i : ZMod p) = (h a : ZMod p)

/-- The actual uniform residue expectation with its active constraints. -/
def giantSignedPrimeResidueExpectation (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  (1 / (p : ℝ)) * ∑ r : ZMod p,
    (if ∀ i ∈ A, r + (h i : ZMod p) = 0 then 1 else 0) *
      ∏ i ∈ Finset.univ \ A, (1 - (1 - q i) * giantSignedPrimeResidueHit p h i r)

/-- The empty and singleton terms of the residue expansion. -/
def giantSignedPrimeResidueBaseline (p : ℕ) {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  1 - (∑ i, (1 - q i)) / (p : ℝ)

/-- An orphan interval has two strict, distinct ghost endpoints. -/
def giantSignedPrimeOrphanWeight (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (l u : Fin n) : ℝ :=
  (-(1 - q l)) * (-(1 - q u)) * giantSignedPrimeOffsetHit p h u l *
    ∏ i ∈ Finset.univ.filter (fun i => l < i ∧ i < u),
      giantSignedPrimeDamping p h q i l

theorem giantSignedPrimeResidueHit_eq_line (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (i : Fin n) (r : ZMod p) :
    giantSignedPrimeResidueHit p h i r =
      markedLineHit (fun j => -(h j : ZMod p)) i r := by
  simp only [giantSignedPrimeResidueHit, markedLineHit, eq_neg_iff_add_eq_zero]

theorem giantSignedPrimeResidueHit_anchor (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (i a : Fin n) :
    giantSignedPrimeResidueHit p h i (-(h a : ZMod p)) =
      giantSignedPrimeOffsetHit p h i a := by
  simp only [giantSignedPrimeResidueHit, giantSignedPrimeOffsetHit, neg_add_eq_zero, eq_comm]

theorem giantSignedPrimeDamping_eq (p : ℕ) {n : ℕ} (h : Fin n → ℤ)
    (q : Fin n → ℝ) (i a : Fin n) :
    giantSignedPrimeDamping p h q i a =
      if (h i : ZMod p) = (h a : ZMod p) then q i else 1 := by
  by_cases hi : (h i : ZMod p) = (h a : ZMod p)
  · simp [giantSignedPrimeDamping, giantSignedPrimeOffsetHit, hi]
  · simp [giantSignedPrimeDamping, giantSignedPrimeOffsetHit, hi]

/-- A nonempty active set pins the residue to its anchor, retaining the
literal compatibility test and every unmarked damping factor. -/
theorem giantSignedPrimeResidueExpectation_active (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (a : Fin n) (ha : a ∈ A) :
    giantSignedPrimeResidueExpectation p h q A = (1 / (p : ℝ)) *
      (if GiantSignedPrimeActiveCompatible p h A a then
        ∏ i ∈ Finset.univ \ A, giantSignedPrimeDamping p h q i a else 0) := by
  classical
  unfold giantSignedPrimeResidueExpectation
  rw [Finset.sum_eq_single (-(h a : ZMod p))]
  · have hactive : (∀ i ∈ A, -(h a : ZMod p) + (h i : ZMod p) = 0) ↔
        GiantSignedPrimeActiveCompatible p h A a := by
      simp only [GiantSignedPrimeActiveCompatible, neg_add_eq_zero, eq_comm]
    simp only [hactive, giantSignedPrimeResidueHit_anchor, giantSignedPrimeDamping,
      ite_mul, one_mul, zero_mul]
  · intro r _ hr
    have hmiss : ¬∀ i ∈ A, r + (h i : ZMod p) = 0 := by
      intro hall
      exact hr (eq_neg_iff_add_eq_zero.mpr (hall a ha))
    simp only [hmiss, ite_false, zero_mul]
  · simp

/-- Incompatible active offsets contribute zero. -/
theorem giantSignedPrimeResidueExpectation_incompatible (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (A : Finset (Fin n))
    (a : Fin n) (ha : a ∈ A) (hc : ¬GiantSignedPrimeActiveCompatible p h A a) :
    giantSignedPrimeResidueExpectation p h q A = 0 := by
  rw [giantSignedPrimeResidueExpectation_active p h q A a ha, ite_eq_right hc, mul_zero]

/-- The exact inactive expectation is its singleton baseline plus a sum
of strict orphan intervals. -/
theorem giantSignedPrimeResidueExpectation_empty (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) :
    giantSignedPrimeResidueExpectation p h q ∅ = giantSignedPrimeResidueBaseline p q +
      (1 / (p : ℝ)) * ∑ l : Fin n,
        ∑ u ∈ Finset.univ.filter (fun u => l < u), giantSignedPrimeOrphanWeight p h q l u := by
  classical
  have hh := marked_memory_orphan_line_average (Finset.univ : Finset (Fin n))
    (fun i => 1 - q i) (fun i => -(h i : ZMod p))
  rw [ZMod.card] at hh
  have hweight (l u : Fin n) :
      (if -(h l : ZMod p) = -(h u : ZMod p) then (1 - q l) * (1 - q u) *
        ∏ i ∈ Finset.univ.filter (fun i => l < i ∧ i < u),
          (1 - (1 - q i) * markedLineHit (fun j => -(h j : ZMod p)) i (-(h l : ZMod p)))
      else 0) = giantSignedPrimeOrphanWeight p h q l u := by
    simp only [← giantSignedPrimeResidueHit_eq_line, giantSignedPrimeResidueHit_anchor,
      giantSignedPrimeOrphanWeight, giantSignedPrimeDamping, giantSignedPrimeOffsetHit,
      neg_inj, neg_mul_neg]
    by_cases hlu : (h l : ZMod p) = (h u : ZMod p)
    · simp only [hlu, ite_true, eq_comm, mul_one]
    · simp only [hlu, ite_false, Ne.symm hlu, mul_zero, zero_mul]
  simp_rw [hweight] at hh
  simpa [giantSignedPrimeResidueExpectation, giantSignedPrimeResidueBaseline,
    giantSignedPrimeResidueHit_eq_line, div_eq_mul_inv, mul_comm] using hh

/-- Dividing by the common baseline charges one reciprocal prime factor
for each strict orphan interval. -/
theorem giantSignedPrimeResidueExpectation_empty_normalized (p : ℕ) [NeZero p] {n : ℕ}
    (h : Fin n → ℤ) (q : Fin n → ℝ) (hb : giantSignedPrimeResidueBaseline p q ≠ 0) :
    giantSignedPrimeResidueExpectation p h q ∅ / giantSignedPrimeResidueBaseline p q =
      1 + (1 / ((p : ℝ) * giantSignedPrimeResidueBaseline p q)) * ∑ l : Fin n,
        ∑ u ∈ Finset.univ.filter (fun u => l < u), giantSignedPrimeOrphanWeight p h q l u := by
  rw [giantSignedPrimeResidueExpectation_empty]
  field_simp

end
end ArtinMatthews
