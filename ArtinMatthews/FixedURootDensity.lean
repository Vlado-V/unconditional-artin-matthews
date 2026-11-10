module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-!
# The exact fixed-u Euler density

The congruence count has density `(φ(u)/u) * (S₁/φ(S₁))`. If `S₁ ∣ u`, the
Euler factors at primes dividing `S₁` cancel. The product identity does not
require `S₁` to be squarefree, although it applies in particular to the
squarefree common-prime part used in PD's root count.
-/

namespace ArtinMatthews

open scoped BigOperators

/-- The real density factor supplied by the fixed-u congruence count. -/
noncomputable def fixedURootDensity (u S₁ : ℕ) : ℝ :=
  ((u.totient : ℝ) / (u : ℝ)) * ((S₁ : ℝ) / (S₁.totient : ℝ))

/-- Euler's product formula, transferred from the exact rational theorem. -/
theorem real_totient_eq_mul_primeFactors (n : ℕ) :
    (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

theorem fixedU_primeFactors_filter_eq_sdiff {u S₁ : ℕ} (hS₁ : 0 < S₁) :
    u.primeFactors.filter (fun p => ¬ p ∣ S₁) = u.primeFactors \ S₁.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hp, hnot⟩
    exact ⟨hp, fun hs => hnot (Nat.dvd_of_mem_primeFactors hs)⟩
  · rintro ⟨hp, hnot⟩
    exact ⟨hp, fun hdiv => hnot ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors hdiv hS₁.ne')⟩

/-- Exact cancellation of the Euler factors at primes dividing the common part. -/
theorem fixedURootDensity_eq_product {u S₁ : ℕ} (hu : 0 < u) (hS₁ : 0 < S₁)
    (hdiv : S₁ ∣ u) :
    fixedURootDensity u S₁ =
      ∏ p ∈ u.primeFactors.filter (fun p => ¬ p ∣ S₁), (1 - (p : ℝ)⁻¹) := by
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hphi0 : (S₁.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hS₁).ne'
  have hsubset : S₁.primeFactors ⊆ u.primeFactors := Nat.primeFactors_mono hdiv hu.ne'
  have hsplit := Finset.prod_sdiff (f := fun p : ℕ => (1 - (p : ℝ)⁻¹)) hsubset
  rw [fixedU_primeFactors_filter_eq_sdiff hS₁]
  unfold fixedURootDensity
  field_simp [hu0, hphi0]
  rw [real_totient_eq_mul_primeFactors u, real_totient_eq_mul_primeFactors S₁, ← hsplit]
  ring_nf

/-- A prime factor of `u` cannot divide the part of the modulus coprime to `u`. -/
theorem fixedU_primeFactors_filter_mul {u S₁ S₂ : ℕ} (hcop : S₂.Coprime u) :
    u.primeFactors.filter (fun p => ¬ p ∣ S₁ * S₂) =
      u.primeFactors.filter (fun p => ¬ p ∣ S₁) := by
  ext p
  by_cases hp : p ∈ u.primeFactors
  · have hprime := Nat.prime_of_mem_primeFactors hp
    have hnot : ¬ p ∣ S₂ := by
      intro hdiv
      have hd : p ∣ 1 := hcop.gcd_eq_one ▸
        Nat.dvd_gcd hdiv (Nat.dvd_of_mem_primeFactors hp)
      exact hprime.ne_one (Nat.dvd_one.mp hd)
    simp only [Finset.mem_filter, hp, true_and, hprime.dvd_mul, hnot, or_false]
  · simp only [Finset.mem_filter, hp, false_and]

/-- The common-prime density may equivalently omit primes dividing the full
squarefree modulus `S₁*S₂`, when `S₂` is coprime to the fixed coordinate. -/
theorem fixedURootDensity_eq_product_modulus {u S₁ S₂ : ℕ}
    (hu : 0 < u) (hS₁ : 0 < S₁) (hdiv : S₁ ∣ u) (hcop : S₂.Coprime u) :
    fixedURootDensity u S₁ =
      ∏ p ∈ u.primeFactors.filter (fun p => ¬ p ∣ S₁ * S₂), (1 - (p : ℝ)⁻¹) := by
  rw [fixedU_primeFactors_filter_mul hcop]
  exact fixedURootDensity_eq_product hu hS₁ hdiv

end ArtinMatthews
