module

public import ArtinMatthews.PrimeExtractionPrimeTestBound
public import ArtinMatthews.MarkedRoughCharacterRange


set_option backward.privateInPublic true
@[expose] public section

/-! Actual coefficient inputs for Proposition 2.1 in section eight.
The long character tests are discharged by the proved cubic Hecke estimate;
rough support and coefficient size are proved for the literal coefficients. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths Filter
open scoped BigOperators Classical

theorem primeExtraction_criterion_frequency_bound (T B : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ X t : ℝ, X ≤ T*x → |t| ≤ 2*X*(Real.log x)^B →
      |t| ≤ x^(2 : ℝ) := by
  have hC : 0 < max 1 T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  have hlog := (isLittleO_log_rpow_rpow_atTop B (show (0:ℝ)<1 by norm_num)).bound
    (by positivity : (0:ℝ)<1/(2*max 1 T))
  filter_upwards [hlog, eventually_gt_atTop (1 : ℝ)] with x hlog hx
  intro X t hX ht
  have hx0 : 0 < x := by linarith
  have hlog' : (Real.log x)^B ≤ x/(2*max 1 T) := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_pos hx).le _), abs_of_pos hx0,
      one_div, div_eq_mul_inv, mul_comm, one_mul] using hlog
  calc
    |t| ≤ 2*X*(Real.log x)^B := ht
    _ ≤ 2*(max 1 T*x)*(Real.log x)^B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hX.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le)) (by norm_num))
        (Real.rpow_nonneg (Real.log_pos hx).le _)
    _ ≤ 2*(max 1 T*x)*(x/(2*max 1 T)) :=
      mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = x^(2 : ℝ) := by rw [Real.rpow_two]; field_simp

theorem primeExtractionFirstPhaseCoefficient_criterion (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B δ D R T γ : ℝ) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (X H : ℝ), X ≤ T*x → x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ v t : ℝ, |v| ≤ (Real.log x)^R → |t| ≤ 2*X*(Real.log x)^B →
      ‖markedTwistedSum (Finset.Icc m n)
        (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ (x^γ) v)
        ϑ t‖ / H ≤ 35*(Real.log x)^(-D) := by
  filter_upwards [primeExtractionFirstPhaseCoefficient_normalized_all_log A hA hnoncube χ
      A₀ 2 δ D R (by norm_num) hδ hD,
    primeExtraction_criterion_frequency_bound T B,
    eventually_gt_atTop (0 : ℝ)] with x hprime hfreq hx
  intro q _ hq ϑ X H hX hH m n hmn hmH hnH v t hv ht
  exact hprime q hq ϑ H hH m n hmn hmH hnH (x^γ) (Real.rpow_nonneg hx.le _) v t hv
    (hfreq X t hX ht)

theorem primeExtraction_phase_coefficients_rough_support
    (η : HeckeFamily.Character) {r : ℕ} (χ : DirichletCharacter ℂ r)
    {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ (j : ℕ) (v : ℝ),
      (∀ m, primeExtractionFirstPhaseCoefficient η χ (x^γ) v m ≠ 0 →
        MarkedRoughAbove (Real.exp ((Real.log x)^(0.24 : ℝ))) m) ∧
      (∀ n, primeExtractionSecondPhaseCoefficient η χ j (x^γ) v n ≠ 0 →
        MarkedRoughAbove (Real.exp ((Real.log x)^(0.24 : ℝ))) n) := by
  filter_upwards [marked_rough_log_cutoff_le_power 0.24 γ (by norm_num) hγ] with x hx
  intro j v
  constructor
  · intro m hm p hp hpm
    exact hx.trans_lt ((primeExtractionFirstPhaseCoefficient_support η χ hm).2.2 p hp hpm)
  · intro n hn p hp hpn
    exact hx.trans_lt ((primeExtractionSecondPhaseCoefficient_support η χ j hn).2.1 p hp hpn)

theorem primeExtraction_phase_coefficients_log_bound
    (η : HeckeFamily.Character) {r : ℕ} (χ : DirichletCharacter ℂ r)
    (J : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, ∀ (j : ℕ), j ≤ J → ∀ z v : ℝ,
      (∀ m, ‖primeExtractionFirstPhaseCoefficient η χ z v m‖ ≤ (Real.log x)^C) ∧
      (∀ n, ‖primeExtractionSecondPhaseCoefficient η χ j z v n‖ ≤ (Real.log x)^C) := by
  have hlarge := (tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop
  filter_upwards [hlarge.eventually (eventually_ge_atTop (max 2 ((2:ℝ)^J)))] with x hx
  intro j hj z v
  constructor
  · intro m
    exact (primeExtractionFirstPhaseCoefficient_norm_le η χ z v m).trans
      ((le_max_left _ _).trans hx)
  · intro n
    exact (primeExtractionSecondPhaseCoefficient_norm_le η χ j z v n).trans
      ((pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : j-1≤J)).trans
        ((le_max_right _ _).trans hx))

end ArtinMatthews
