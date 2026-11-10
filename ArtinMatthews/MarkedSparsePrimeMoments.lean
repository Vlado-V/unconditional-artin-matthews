module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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
public import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLargeValues


set_option backward.privateInPublic true
@[expose] public section

/-! The growing-degree prime moment from the marked major-arc argument,
using the fully proved OAI separated moment theorem. The coefficient vector
is the actual shifted character vector, with its normalization retained. -/

namespace ArtinMatthews

open scoped BigOperators
open OAI.TwoPointCorrelations

noncomputable section

def markedPrimePhase (p : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((Real.log (p : ℝ) * t : ℝ) : ℂ) * Complex.I)

def markedPrimePolynomial {k : ℕ} (P : Finset ℕ) (H : ℝ)
    (χ : DirichletCharacter ℂ k) (ξ t : ℝ) : ℂ :=
  (∑ p ∈ P, χ p * markedPrimePhase p (t + ξ)) / H

def markedPrimeCoefficient {k : ℕ} (H : ℝ)
    (χ : DirichletCharacter ℂ k) (ξ : ℝ) (p : ℕ) : ℂ :=
  χ p * markedPrimePhase p ξ / H

@[simp] theorem markedPrimePhase_norm (p : ℕ) (t : ℝ) :
    ‖markedPrimePhase p t‖ = 1 := by
  rw [markedPrimePhase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Real.exp_zero]

theorem markedPrimePhase_add (p : ℕ) (t ξ : ℝ) :
    markedPrimePhase p (t + ξ) = markedPrimePhase p ξ * markedPrimePhase p t := by
  unfold markedPrimePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The sign change puts the paper's positive imaginary powers into the
upstream convention with frequencies `-log p`. -/
theorem markedPrimePolynomial_eq_mrt {k : ℕ} (P : Finset ℕ) (H : ℝ)
    (χ : DirichletCharacter ℂ k) (ξ t : ℝ) :
    markedPrimePolynomial P H χ ξ t =
      mrtExponentialPolynomial P (markedPrimeCoefficient H χ ξ)
        (fun p => -Real.log (p : ℝ)) (-t) := by
  classical
  unfold markedPrimePolynomial mrtExponentialPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  rw [markedPrimePhase_add]
  simp only [markedPrimeCoefficient, markedPrimePhase, neg_mul_neg]
  ring

theorem markedPrimeCoefficient_norm_le {k : ℕ} (H : ℝ) (hH : 0 < H)
    (χ : DirichletCharacter ℂ k) (ξ : ℝ) (p : ℕ) :
    ‖markedPrimeCoefficient H χ ξ p‖ ≤ 1 / H := by
  simp only [markedPrimeCoefficient, norm_div, norm_mul, markedPrimePhase_norm,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  exact div_le_div_of_nonneg_right (χ.norm_le_one _) hH.le

theorem markedPrimeCoefficient_square_mass {k : ℕ} (P : Finset ℕ)
    (H : ℝ) (hH : 0 < H) (χ : DirichletCharacter ℂ k) (ξ : ℝ) :
    (∑ p ∈ P, ‖markedPrimeCoefficient H χ ξ p‖ ^ 2) ≤ (P.card : ℝ) / H ^ 2 := by
  calc
    _ ≤ ∑ _p ∈ P, (1 / H) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (norm_nonneg _) (markedPrimeCoefficient_norm_le H hH χ ξ p) 2
    _ = _ := by simp [div_eq_mul_inv]


/-- The full factorial moment bound for arbitrary degree, uniformly in the
real shift and the Dirichlet character, including its zero values. -/
theorem markedPrimePolynomial_separated_moment {k : ℕ}
    (P : Finset ℕ) (H : ℝ) (hH : 0 < H) (χ : DirichletCharacter ℂ k) (ξ : ℝ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T) (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) :
    (∑ t ∈ S, ‖markedPrimePolynomial P H χ ξ t‖ ^ (2*r)) ≤
      8 * Real.exp 1 * (T + 1 + (N^r : ℕ)) *
        (2 + (Real.log (N^r : ℕ))^2) *
        (r.factorial : ℝ) * ((P.card : ℝ) / H^2)^r := by
  classical
  have hnegS : ∀ t ∈ S.image Neg.neg, |t| ≤ T := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    simpa only [abs_neg] using hS u hu
  have hnegsep : ∀ x ∈ S.image Neg.neg, ∀ y ∈ S.image Neg.neg,
      x ≠ y → 1 ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun h => hxy (congrArg Neg.neg h)
    simpa only [neg_sub_neg, abs_sub_comm] using hsep u hu v hv huv
  have hm := mrt_prime_separated_moment P (markedPrimeCoefficient H χ ξ)
    N r hP hN (S.image Neg.neg) hT hnegS hnegsep
  rw [Finset.sum_image (fun _ _ _ _ h => neg_injective h)] at hm
  simp_rw [← markedPrimePolynomial_eq_mrt] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => sq_nonneg _))
      (markedPrimeCoefficient_square_mass P H hH χ ξ) r) (by positivity))

/-- An explicit large-value count obtained from the actual shifted prime
polynomial. The degree may grow with the scale. -/
theorem markedPrimePolynomial_large_values {k : ℕ}
    (P : Finset ℕ) (H : ℝ) (hH : 0 < H) (χ : DirichletCharacter ℂ k) (ξ : ℝ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (hlarge : ∀ t ∈ S, V ≤ ‖markedPrimePolynomial P H χ ξ t‖) :
    (S.card : ℝ) ≤
      (8 * Real.exp 1 * (T + 1 + (N^r : ℕ)) *
        (2 + (Real.log (N^r : ℕ))^2) *
        (r.factorial : ℝ) * ((P.card : ℝ) / H^2)^r) / V^(2*r) := by
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∑ _t ∈ S, V^(2*r) := by simp
    _ ≤ ∑ t ∈ S, ‖markedPrimePolynomial P H χ ξ t‖^(2*r) := by
      exact Finset.sum_le_sum fun t ht => pow_le_pow_left₀ hV.le (hlarge t ht) _
    _ ≤ _ := markedPrimePolynomial_separated_moment P H hH χ ξ N r hP hN S hT hS hsep

end
end ArtinMatthews
