module

public import ArtinMatthews.MarkedMajorLabelPolynomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The literal remaining prime-label polynomial. Its support restriction
is independent of the isolated prime, and its norm is bounded by the
actual reciprocal coefficient mass. -/
namespace ArtinMatthews
open Finset

noncomputable def markedMajorCofactorSet {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (a b Y H : ℝ) : Finset ℕ := by
  classical
  exact (markedMajorLabelSet P).filter (fun n => a*Y/(2*H) ≤ (n:ℝ) ∧ (n:ℝ) ≤ b*Y/H)

noncomputable def markedMajorCofactorPolynomial {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (R : Finset ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Y H t : ℝ) : ℂ :=
  ((H/Y:ℝ):ℂ)*∑ n ∈ R,(markedMajorLabelMass P:ℂ)*χ n*markedPrimePhase n t

theorem markedMajorCofactorPolynomial_norm_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j,0 < bandReciprocalMass (P j))
    (R : Finset ℕ) (hR : R ⊆ markedMajorLabelSet P)
    {B Y H : ℝ} (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 < H)
    (hcap : ∀ n ∈ R,(n:ℝ) ≤ B*Y/H) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖markedMajorCofactorPolynomial P R χ Y H t‖ ≤ B := by
  have hMass := markedMajorLabelMass_pos P hV
  have hm : (∑ n ∈ R,markedMajorLabelMass P/(n:ℝ)) ≤ 1 := by
    rw [← markedMajorLabelSet_reciprocal_mass P hP hdis hV]
    exact sum_le_sum_of_subset_of_nonneg hR (fun n _ _ => by positivity)
  have ht : ∀ n ∈ R,‖(markedMajorLabelMass P:ℂ)*χ n*markedPrimePhase n t‖ ≤
      (B*Y/H)*(markedMajorLabelMass P/(n:ℝ)) := by
    intro n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast markedMajorLabelSet_pos P hP (hR hn)
    simp only [norm_mul,markedPrimePhase_norm,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hMass]
    calc
      _ ≤ markedMajorLabelMass P := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (χ.norm_le_one n) hMass.le
      _ ≤ _ := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hnpos).mpr
        nlinarith [mul_le_mul_of_nonneg_right (hcap n hn) hMass.le]
  unfold markedMajorCofactorPolynomial
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hH hY)]
  calc
    _ ≤ (H/Y)*∑ n ∈ R,(B*Y/H)*(markedMajorLabelMass P/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum ht)) (by positivity)
    _ = (H/Y)*(B*Y/H)*(∑ n ∈ R,markedMajorLabelMass P/(n:ℝ)) := by rw [← mul_sum]; ring
    _ ≤ (H/Y)*(B*Y/H)*1 := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = B := by field_simp

theorem markedMajorCofactorPolynomial_continuous {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (R : Finset ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (Y H : ℝ) :
    Continuous (markedMajorCofactorPolynomial P R χ Y H) := by
  unfold markedMajorCofactorPolynomial markedPrimePhase
  fun_prop

theorem markedMajorCofactorSet_cutoff {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (η : ℝ → ℂ) {a b Y H : ℝ}
    (hsupp : Function.support η ⊆ Set.Icc a b) (hY : 0 < Y) (hH : 0 < H)
    {p n : ℕ} (hp : H ≤ (p:ℝ)) (hp2 : (p:ℝ) ≤ 2*H)
    (hn : n ∈ markedMajorLabelSet P) (hη : η ((p*n:ℕ)/Y) ≠ 0) :
    n ∈ markedMajorCofactorSet P a b Y H := by
  classical
  have hsupport := hsupp hη
  have hlow : a*Y ≤ (p:ℝ)*(n:ℝ) := by
    simpa only [Nat.cast_mul] using (le_div_iff₀ hY).mp hsupport.1
  have hhigh : (p:ℝ)*(n:ℝ) ≤ b*Y := by
    simpa only [Nat.cast_mul] using (div_le_iff₀ hY).mp hsupport.2
  apply mem_filter.mpr
  refine ⟨hn,?_,?_⟩
  · apply (div_le_iff₀ (show 0 < 2*H by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp2 (Nat.cast_nonneg n : (0:ℝ)≤n)]
  · apply (le_div_iff₀ hH).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n : (0:ℝ)≤n)]

end ArtinMatthews
