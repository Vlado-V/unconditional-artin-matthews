module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.MarkedTypeIIArithmetic
public import ArtinMatthews.ShiftedBilinear
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# The exact finite reduction to the marked determinant square

These are the algebraic steps preceding the analytic replacement in PD §3.1.
They retain arbitrary coefficients and an arbitrary band-invariant function.
The collision term is displayed explicitly, not discarded or assumed small.
No minor-arc replacement or major-term saving is asserted here.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ArtinMatthews

/-- Invariance under one permitted divisor implies invariance under every
finite product of permitted divisors, including repeated prime powers. -/
theorem marked_invariant_finset_product {ι : Type*} (I : Finset ι)
    (p : ι → ℕ) (F : ℕ → ℂ)
    (hp : ∀ i ∈ I, 0 < p i)
    (hF : ∀ i ∈ I, ∀ h : ℕ, 0 < h → F (p i * h) = F h)
    {h : ℕ} (hh : 0 < h) :
    F ((∏ i ∈ I, p i) * h) = F h := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi, mul_assoc]
    rw [hF i (Finset.mem_insert_self _ _) _
      (Nat.mul_pos (Finset.prod_pos (fun j hj => hp j (Finset.mem_insert_of_mem hj))) hh)]
    exact ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- On a represented predecessor, band-prime invariance gives exactly the
common-quotient value of `F`. No restriction is placed on the values of `F`
beyond the stated invariance. -/
theorem marked_invariant_represented {ι : Type*} (I : Finset ι)
    (p : ι → ℕ) (F : ℕ → ℂ)
    (hp : ∀ i ∈ I, 0 < p i)
    (hF : ∀ i ∈ I, ∀ h : ℕ, 0 < h → F (p i * h) = F h)
    {m n h : ℕ} (hh : 0 < h)
    (hrep : m * n = 1 + (∏ i ∈ I, p i) * h) :
    F (m * n - 1) = F h := by
  rw [hrep, Nat.add_sub_cancel_left]
  exact marked_invariant_finset_product I p F hp hF hh

/-- A label product and the two unmarked factors at one endpoint. -/
structure MarkedTypeIIEndpoint where
  label : ℕ
  leftFactor : ℕ
  rightFactor : ℕ
  deriving DecidableEq

def MarkedTypeIIEndpoint.value (e : MarkedTypeIIEndpoint) : ℕ :=
  e.leftFactor * e.rightFactor

/-- The equation `mn-1=ah`, expressed without truncated natural subtraction. -/
abbrev MarkedTypeIIEndpoint.represents (e : MarkedTypeIIEndpoint) (h : ℕ) : Prop :=
  e.value = 1 + e.label * h

/-- The endpoint coefficient includes the label cutoff and both scalar factors. -/
def markedTypeIIEndpointCoeff (η α β : ℕ → ℂ) (e : MarkedTypeIIEndpoint) : ℂ :=
  η e.label * α e.leftFactor * β e.rightFactor

/-- The inner endpoint sum at the common quotient `h`. -/
def markedTypeIIEndpointSum (E : Finset MarkedTypeIIEndpoint)
    (c : MarkedTypeIIEndpoint → ℂ) (h : ℕ) : ℂ :=
  ∑ e ∈ E, if e.represents h then c e else 0

/-- The nonnegative Cauchy square before the common quotient is eliminated. -/
def markedTypeIICauchySquare (E : Finset MarkedTypeIIEndpoint)
    (H : Finset ℕ) (c : MarkedTypeIIEndpoint → ℂ) : ℝ :=
  ∑ h ∈ H, ‖markedTypeIIEndpointSum E c h‖ ^ 2

theorem markedTypeIICauchySquare_nonneg (E : Finset MarkedTypeIIEndpoint)
    (H : Finset ℕ) (c : MarkedTypeIIEndpoint → ℂ) :
    0 ≤ markedTypeIICauchySquare E H c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The arbitrary bounded endpoint function is removed only by Cauchy.
The right side retains the exact, nonnegative, common-quotient square. -/
theorem marked_typeII_cauchy (E : Finset MarkedTypeIIEndpoint)
    (H : Finset ℕ) (c : MarkedTypeIIEndpoint → ℂ) (F : ℕ → ℂ)
    (hF : ∀ h ∈ H, ‖F h‖ ≤ 1) :
    ‖∑ h ∈ H, F h * markedTypeIIEndpointSum E c h‖ ^ 2 ≤
      (H.card : ℝ) * markedTypeIICauchySquare E H c := by
  calc
    _ ≤ (∑ h ∈ H, ‖markedTypeIIEndpointSum E c h‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hF h hh)
    _ ≤ _ := by
      simpa [markedTypeIICauchySquare] using
        Finset.sum_mul_sq_le_sq_mul_sq H (fun _ => (1 : ℝ))
          (fun h => ‖markedTypeIIEndpointSum E c h‖)

/-- Exact expansion of the Cauchy square, before using coprimality of labels. -/
theorem marked_typeII_square_expansion (E : Finset MarkedTypeIIEndpoint)
    (H : Finset ℕ) (c : MarkedTypeIIEndpoint → ℂ) :
    markedTypeIICauchySquare E H c =
      (∑ e ∈ E, ∑ f ∈ E, c e * conj (c f) *
        ∑ h ∈ H, if e.represents h ∧ f.represents h then (1 : ℂ) else 0).re := by
  simpa [markedTypeIICauchySquare, markedTypeIIEndpointSum, mul_ite, ite_mul,
    ← ite_and, and_comm] using
      (bilinear_energy_eq_correlations E H c
        (fun e h => if e.represents h then (1 : ℂ) else 0))

/-- The signed determinant at two endpoints. -/
abbrev markedTypeIIDeterminant (e f : MarkedTypeIIEndpoint) : ℤ :=
  (f.label : ℤ) * e.value - (e.label : ℤ) * f.value

/-- The coprime-label part of the square after eliminating the common quotient. -/
def markedTypeIIDeterminantSum (E : Finset MarkedTypeIIEndpoint)
    (c : MarkedTypeIIEndpoint → ℂ) : ℂ :=
  ∑ e ∈ E, ∑ f ∈ E,
    if e.label.Coprime f.label ∧
        markedTypeIIDeterminant e f = (f.label : ℤ) - e.label
    then c e * conj (c f) else 0

/-- The coincident-label contribution remains an explicit finite sum. -/
def markedTypeIICollisionSum (E : Finset MarkedTypeIIEndpoint)
    (H : Finset ℕ) (c : MarkedTypeIIEndpoint → ℂ) : ℂ :=
  ∑ e ∈ E, ∑ f ∈ E,
    if e.label.Coprime f.label then 0 else
      c e * conj (c f) *
        ∑ h ∈ H, if e.represents h ∧ f.represents h then (1 : ℂ) else 0

/-- Exact determinant reduction with the collision contribution retained.
The cutoff bound is only used to ensure every possible common quotient occurs
in the finite `range B`. -/
theorem marked_typeII_square_eq_determinant_add_collisions_of_mul_bound
    (E : Finset MarkedTypeIIEndpoint) (B : ℕ) (c : MarkedTypeIIEndpoint → ℂ)
    (he : ∀ e ∈ E, 0 < e.label ∧ 1 ≤ e.value ∧ e.value ≤ e.label * B) :
    markedTypeIICauchySquare E (Finset.range B) c =
      (markedTypeIIDeterminantSum E c +
        markedTypeIICollisionSum E (Finset.range B) c).re := by
  rw [marked_typeII_square_expansion]
  congr 1
  unfold markedTypeIIDeterminantSum markedTypeIICollisionSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e heE
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hfE
  by_cases hcop : e.label.Coprime f.label
  · rw [ite_eq_left hcop, add_zero]
    have hmul : (∑ h ∈ Finset.range B, c e * conj (c f) *
        (if e.represents h ∧ f.represents h then (1 : ℂ) else 0)) =
        ∑ h ∈ Finset.range B,
          if e.represents h ∧ f.represents h then c e * conj (c f) else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> ring
    have hsum : c e * conj (c f) *
        (∑ h ∈ Finset.range B, if e.represents h ∧ f.represents h then (1 : ℂ) else 0) =
        if markedTypeIIDeterminant e f = (f.label : ℤ) - e.label
          then c e * conj (c f) else 0 := by
      rw [Finset.mul_sum, hmul]
      simpa only [markedTypeIIDeterminant, MarkedTypeIIEndpoint.represents] using
        marked_commonQuotient_sum_of_mul_bound (he e heE).1 hcop
          (he e heE).2.1 (he f hfE).2.1 (he e heE).2.2 (c e * conj (c f))
    rw [hsum]
    by_cases hdet : markedTypeIIDeterminant e f = (f.label : ℤ) - e.label
    · rw [ite_eq_left hdet, ite_eq_left (And.intro hcop hdet)]
    · rw [ite_eq_right hdet, ite_eq_right (fun h => hdet h.2)]
  · simp [hcop]

/-- The simpler endpoint-bound version of the exact determinant reduction. -/
theorem marked_typeII_square_eq_determinant_add_collisions
    (E : Finset MarkedTypeIIEndpoint) (B : ℕ) (c : MarkedTypeIIEndpoint → ℂ)
    (he : ∀ e ∈ E, 0 < e.label ∧ 1 ≤ e.value ∧ e.value ≤ B) :
    markedTypeIICauchySquare E (Finset.range B) c =
      (markedTypeIIDeterminantSum E c +
        markedTypeIICollisionSum E (Finset.range B) c).re := by
  apply marked_typeII_square_eq_determinant_add_collisions_of_mul_bound
  intro e heE
  refine ⟨(he e heE).1, (he e heE).2.1, (he e heE).2.2.trans ?_⟩
  simpa using Nat.mul_le_mul_right B (show 1 ≤ e.label from (he e heE).1)

end ArtinMatthews
