module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Quantitative fixed-power scale choice for the direct finite circle
detector. These real-power inequalities contain no spectral assertion. -/

noncomputable section
namespace ArtinMatthews

def circlePowerScale (P A : ℝ) : ℕ := ⌈P^A⌉₊

def circlePowerQ (P A : ℝ) : ℝ := 3 * circlePowerScale P A

theorem circlePowerScale_pos {P A : ℝ} (hP : 0 < P) : 0 < circlePowerScale P A :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hP A)

theorem circlePowerScale_bounds {P A : ℝ} (hP : 2 ≤ P) (hA : 0 ≤ A) :
    P^A ≤ circlePowerScale P A ∧ (circlePowerScale P A : ℝ) ≤ 2 * P^A := by
  have hpow : 1 ≤ P^A := Real.one_le_rpow (by linarith) hA
  refine ⟨Nat.le_ceil _, ?_⟩
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith : 0 ≤ P) A)
  change (⌈P^A⌉₊ : ℝ) ≤ _
  linarith

theorem circlePowerQ_le {P A : ℝ} (hP : 2 ≤ P) (hA : 0 ≤ A) :
    circlePowerQ P A ≤ P^(A+3) := by
  have hP0 : 0 < P := by linarith
  have hscale := (circlePowerScale_bounds hP hA).2
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hP 3
  norm_num at hcube
  have h6 : (6 : ℝ) ≤ P^(3 : ℝ) := by
    norm_num [Real.rpow_natCast]
    linarith
  unfold circlePowerQ
  rw [Real.rpow_add hP0]
  nlinarith [mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hP0.le A)]

theorem circlePowerScale_threshold {P A b : ℝ} {F r : ℕ}
    (hP : 2 ≤ P) (_hb : 0 ≤ b) (hA : 2*b+2 ≤ A)
    (hF : (F : ℝ) ≤ P^b) (hr : (r : ℝ) ≤ P^b) :
    4*(F*r) ≤ circlePowerScale P A := by
  have hP0 : 0 < P := by linarith
  have hprod : ((F*r : ℕ) : ℝ) ≤ P^(2*b) := by
    calc
      _ = (F : ℝ)*(r : ℝ) := by norm_cast
      _ ≤ P^b * P^b := mul_le_mul hF hr (Nat.cast_nonneg r) (Real.rpow_nonneg hP0.le b)
      _ = P^(2*b) := by rw [← Real.rpow_add hP0]; congr 1; ring
  have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hP 2
  norm_num at hsquare
  have h4 : (4 : ℝ) ≤ P^(2 : ℝ) := by simpa only [Real.rpow_two] using hsquare
  have hlow : (4 : ℝ) * ((F*r : ℕ) : ℝ) ≤ P^A := by
    calc
      _ ≤ P^(2 : ℝ) * P^(2*b) :=
        mul_le_mul h4 hprod (Nat.cast_nonneg _) (Real.rpow_nonneg hP0.le _)
      _ = P^(2*b+2) := by rw [← Real.rpow_add hP0]; congr 1; ring
      _ ≤ P^A := Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  have hceil : P^A ≤ (circlePowerScale P A : ℝ) := Nat.le_ceil _
  exact_mod_cast hlow.trans hceil

theorem circlePowerScale_sqrt_lower {P A : ℝ} (hP : 0 < P) :
    P^(A/2) ≤ Real.sqrt (circlePowerScale P A) := by
  have h := Real.sqrt_le_sqrt (Nat.le_ceil (P^A))
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP.le] at h
  simpa only [circlePowerScale, div_eq_mul_inv, one_mul] using h

theorem circlePowerScale_decay {P A B T : ℝ} (hP : 2 ≤ P)
    (hA : 2*(B+T) ≤ A) :
    P^B / Real.sqrt (circlePowerScale P A) ≤ P^(-T) := by
  have hP0 : 0 < P := by linarith
  calc
    _ ≤ P^B / P^(A/2) := div_le_div_of_nonneg_left (Real.rpow_nonneg hP0.le B)
      (Real.rpow_pos_of_pos hP0 _) (circlePowerScale_sqrt_lower hP0)
    _ = P^(B-A/2) := (Real.rpow_sub hP0 _ _).symm
    _ ≤ P^(-T) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- A budget for every polynomially bounded subpower loss. The exponent
is chosen after the fixed modulus-scale power and the target loss. -/
theorem circle_epsilon_budget {a b u v w ν δ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hν : 0 < ν) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ∀ P Q r : ℝ, 1 ≤ P → 0 ≤ Q → 0 ≤ r →
      Q ≤ P^a → r ≤ P^b → Q^(u*ε) * r^(v*ε) * P^(w*ε) ≤ P^ν := by
  let K := a*u+b*v+w
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let ε := min δ (ν/(K+1))
  have hε : 0 < ε := lt_min hδ (div_pos hν (by linarith))
  refine ⟨ε, hε, min_le_left _ _, ?_⟩
  intro P Q r hP hQ hr hQa hrb
  have hP0 : 0 < P := by linarith
  have hbudget : K*ε ≤ ν := by
    have hh : ε*(K+1) ≤ ν := (le_div_iff₀ (by linarith : 0 < K+1)).mp (min_le_right _ _)
    nlinarith
  have hq := Real.rpow_le_rpow hQ hQa (mul_nonneg hu hε.le)
  have hrr := Real.rpow_le_rpow hr hrb (mul_nonneg hv hε.le)
  calc
    _ ≤ ((P^a)^(u*ε)) * ((P^b)^(v*ε)) * P^(w*ε) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hq hrr (Real.rpow_nonneg hr _) (Real.rpow_nonneg (Real.rpow_nonneg hP0.le _) _))
        (Real.rpow_nonneg hP0.le _)
    _ = P^(K*ε) := by
      rw [← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le,
        ← Real.rpow_add hP0, ← Real.rpow_add hP0]
      congr 1
      dsimp [K]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hbudget

end ArtinMatthews
