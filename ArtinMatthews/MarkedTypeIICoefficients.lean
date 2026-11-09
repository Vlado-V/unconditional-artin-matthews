module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exact long-frequency coefficient symmetries for marked Type II

The coefficient criterion tests every logarithmic-modulus Dirichlet character
and every frequency in a symmetric long interval. Conjugation preserves these
tests with exactly the same radius and constant. No cancellation estimate is
asserted without a corresponding bound on the original scalar coefficient.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ArtinMatthews

/-- Every prime divisor of a rough integer lies above the real cutoff. -/
def MarkedRoughAbove (W : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → W < (p : ℝ)

/-- Rough variables are units at every smaller positive modulus. -/
theorem marked_rough_coprime {W : ℝ} {n k : ℕ} (hk : 0 < k)
    (hkW : (k : ℝ) ≤ W) (hn : MarkedRoughAbove W n) : n.Coprime k := by
  by_contra hcop
  obtain ⟨p, hp, hpn, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpk' : (p : ℝ) ≤ k := by exact_mod_cast Nat.le_of_dvd hk hpk
  exact (not_lt_of_ge (hpk'.trans hkW)) (hn p hp hpn)

theorem marked_rough_unit {W : ℝ} {n k : ℕ} (hk : 0 < k)
    (hkW : (k : ℝ) ≤ W) (hn : MarkedRoughAbove W n) : IsUnit (n : ZMod k) :=
  (ZMod.isUnit_iff_coprime n k).mpr (marked_rough_coprime hk hkW hn)

/-- Every fixed power of `log x` lies below the Type II roughness cutoff for
sufficiently large `x`. The threshold may depend on the fixed exponent. -/
theorem marked_log_modulus_below_roughness {A : ℝ} (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ A ≤ Real.exp ((Real.log x) ^ (0.24 : ℝ)) := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.24)).bound
    (by positivity : (0 : ℝ) < 1 / A)
  have hL : ∀ᶠ L : ℝ in Filter.atTop,
      L ^ A ≤ Real.exp (L ^ (0.24 : ℝ)) := by
    filter_upwards [hsmall, Filter.eventually_gt_atTop (1 : ℝ)] with L hsmall hL
    have hL0 : 0 < L := by linarith
    have hlog : 0 ≤ Real.log L := (Real.log_pos hL).le
    have hpow : 0 ≤ L ^ (0.24 : ℝ) := Real.rpow_nonneg hL0.le _
    simp only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] at hsmall
    rw [Real.rpow_def_of_pos hL0]
    apply Real.exp_le_exp.mpr
    have := (le_div_iff₀ hA).mp
      (show Real.log L ≤ L ^ (0.24 : ℝ) / A by
        simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hsmall)
    nlinarith
  exact Real.tendsto_log_atTop.eventually hL

/-- The actual logarithmic moduli in (2.5) act by units on the rough support. -/
theorem marked_rough_units_eventually {A : ℝ} (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k n : ℕ, 0 < k → (k : ℝ) ≤ (Real.log x) ^ A →
      MarkedRoughAbove (Real.exp ((Real.log x) ^ (0.24 : ℝ))) n →
      IsUnit (n : ZMod k) := by
  filter_upwards [marked_log_modulus_below_roughness hA] with x hx k n hk hkx hn
  exact marked_rough_unit hk (hkx.trans hx) hn

/-- The logarithmic twist `n^(it)`, written exponentially. -/
def markedLogTwist (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t * Real.log (n : ℝ) : ℝ))

theorem markedLogTwist_norm (n : ℕ) (t : ℝ) : ‖markedLogTwist n t‖ = 1 := by
  rw [markedLogTwist, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

theorem markedLogTwist_conj (n : ℕ) (t : ℝ) :
    conj (markedLogTwist n t) = markedLogTwist n (-t) := by
  rw [markedLogTwist, markedLogTwist, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/-- On the positive integer support this is exactly the complex power in (2.5). -/
theorem markedLogTwist_eq_cpow {n : ℕ} (hn : 0 < n) (t : ℝ) :
    markedLogTwist n t = (n : ℂ) ^ (Complex.I * t) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  unfold markedLogTwist
  congr 1
  push_cast
  ring

/-- The scalar Dirichlet-twisted sum on an arbitrary finite coefficient interval. -/
def markedTwistedSum (S : Finset ℕ) (α : ℕ → ℂ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (t : ℝ) : ℂ :=
  ∑ n ∈ S, α n * χ n * markedLogTwist n t

/-- Conjugating the coefficient and character reverses the real frequency. -/
theorem markedTwistedSum_conjugate (S : Finset ℕ) (α : ℕ → ℂ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (t : ℝ) :
    markedTwistedSum S (fun n => conj (α n)) (star χ) t =
      conj (markedTwistedSum S α χ (-t)) := by
  simp [markedTwistedSum, map_sum, map_mul, markedLogTwist_conj, MulChar.star_apply]

theorem markedTwistedSum_norm_conjugate (S : Finset ℕ) (α : ℕ → ℂ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (t : ℝ) :
    ‖markedTwistedSum S (fun n => conj (α n)) (star χ) t‖ =
      ‖markedTwistedSum S α χ (-t)‖ := by
  rw [markedTwistedSum_conjugate, Complex.norm_conj]

/-- The exact normalized bound from (2.5) transfers to the conjugated endpoint,
without increasing its long-frequency radius, modulus bound, or constant. -/
theorem marked_twisted_bound_conjugate (S : Finset ℕ) (α : ℕ → ℂ)
    (H T C : ℝ) (Q : ℕ)
    (hα : ∀ k ≤ Q, ∀ χ : DirichletCharacter ℂ k, ∀ t : ℝ, |t| ≤ T →
      ‖markedTwistedSum S α χ t‖ / H ≤ C) :
    ∀ k ≤ Q, ∀ χ : DirichletCharacter ℂ k, ∀ t : ℝ, |t| ≤ T →
      ‖markedTwistedSum S (fun n => conj (α n)) χ t‖ / H ≤ C := by
  intro k hk χ t ht
  have hbound := hα k hk (star χ) (-t) (by simpa using ht)
  have heq := markedTwistedSum_norm_conjugate S α (star χ) t
  simp only [star_star] at heq
  rw [heq]
  exact hbound

/-- Both endpoint frequencies of the retained Mellin rectangle lie in the
original long-frequency window. The variables `R` and `X` stand for `L^B` and X. -/
theorem marked_retained_frequency_bounds {X R s t : ℝ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hs : |s| ≤ R) (ht : |t| ≤ X * R) :
    |t| ≤ 2 * X * R ∧ |s - t| ≤ 2 * X * R := by
  constructor
  · nlinarith [abs_nonneg t]
  · have htri := abs_sub_le s 0 t
    simp only [sub_zero, zero_sub, abs_neg] at htri
    nlinarith [mul_nonneg (sub_nonneg.mpr hX) hR]

end ArtinMatthews
