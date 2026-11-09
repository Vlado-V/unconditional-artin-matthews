module

public import ArtinMatthews.SourceComparisonPolynomialMean
public import ArtinMatthews.GiantOrderedProductMoment


set_option backward.privateInPublic true
@[expose] public section

/-! The coarse ordinary mean square of the literal uncut product boxes. -/

namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

def sourceComparisonTriplePosition (v : ℕ × ℕ × ℕ) : ℕ :=
  v.1*v.2.1*v.2.2

def sourceComparisonTripleCoefficient (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ)
    (Z : ℝ) (n : ℕ) : ℂ :=
  (∑ v ∈ S.filter (fun v => sourceComparisonTriplePosition v=n), c v)/Z

theorem sourceComparisonTriplePolynomial_eq
    (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ) (N : ℕ)
    (hS : ∀ v ∈ S, sourceComparisonTriplePosition v ∈ Ioc 0 N)
    (Z : ℝ) (g : ℕ → ℂ) (t : ℝ) :
    markedNaturalPolynomial (Ioc 0 N) (fun n => sourceComparisonTripleCoefficient S c Z n*g n) t =
      (∑ v ∈ S, c v*g (sourceComparisonTriplePosition v)*markedPrimePhase
        (sourceComparisonTriplePosition v) t)/Z := by
  unfold markedNaturalPolynomial sourceComparisonTripleCoefficient
  rw [sum_div, ← sum_fiberwise_of_maps_to hS]
  apply sum_congr rfl
  intro n _
  dsimp only
  rw [sum_div, sum_mul, sum_mul]
  apply sum_congr rfl
  intro v hv
  rw [(mem_filter.mp hv).2]
  ring

private theorem triple_fiber_card_le (S : Finset (ℕ × ℕ × ℕ)) {n : ℕ} (hn : 0 < n) :
    (S.filter (fun v => sourceComparisonTriplePosition v=n)).card ≤
      (giantOrderedProductFiber 3 n).card := by
  let f (v : ℕ × ℕ × ℕ) : Fin 3 → ℕ := ![v.1, v.2.1, v.2.2]
  apply card_le_card_of_injOn f
  · rintro ⟨p,m,r⟩ hv
    have he : p*m*r=n := (mem_filter.mp hv).2
    have hpos : 0 < p*m*r := he ▸ hn
    have hp := Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hpos)
    have hm := Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hpos)
    have hr := Nat.pos_of_mul_pos_left hpos
    apply mem_giantOrderedProductFiber.mpr
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · have h0 : f (p,m,r) 0 = p := rfl
      have h1 : f (p,m,r) 1 = m := rfl
      have h2 : f (p,m,r) 2 = r := rfl
      rw [Fin.prod_univ_three, h0, h1, h2]
      simpa only [mul_assoc] using he
  · rintro ⟨p,m,r⟩ _ ⟨p',m',r'⟩ _ h
    have hp : p = p' := congrFun h 0
    have hm : m = m' := congrFun h 1
    have hr : r = r' := congrFun h 2
    simp only [hp, hm, hr]

theorem sourceComparisonTripleCoefficient_square_mass
    (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ) (N : ℕ) (Z M : ℝ)
    (hZ : 0 < Z) (hM : 0 ≤ M) (hc : ∀ v ∈ S, ‖c v‖ ≤ M) :
    (∑ n ∈ Ioc 0 N, ‖sourceComparisonTripleCoefficient S c Z n‖^2) ≤
      (M/Z)^2*(N:ℝ)*(1+Real.log (N:ℝ))^(9:ℕ) := by
  have hpoint (n : ℕ) (hn : n ∈ Ioc 0 N) :
      ‖sourceComparisonTripleCoefficient S c Z n‖ ≤
        (M/Z)*((giantOrderedProductFiber 3 n).card:ℝ) := by
    let F := S.filter (fun v => sourceComparisonTriplePosition v=n)
    unfold sourceComparisonTripleCoefficient
    change ‖(∑ v ∈ F, c v)/(Z:ℂ)‖ ≤ _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
    have hcard : (F.card:ℝ) ≤ (giantOrderedProductFiber 3 n).card := by
      exact_mod_cast triple_fiber_card_le S (mem_Ioc.mp hn).1
    calc
      _ ≤ (∑ _v ∈ F, M)/Z := div_le_div_of_nonneg_right
        ((norm_sum_le _ _).trans (sum_le_sum fun v hv => hc v (mem_filter.mp hv).1)) hZ.le
      _ = (M/Z)*(F.card:ℝ) := by simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard (div_nonneg hM hZ.le)
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ((M/Z)*((giantOrderedProductFiber 3 n).card:ℝ))^2 :=
      sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) (hpoint n hn) 2
    _ = (M/Z)^2*∑ n ∈ Ioc 0 N, ((giantOrderedProductFiber 3 n).card:ℝ)^2 := by
      simp only [mul_pow, mul_sum]
    _ ≤ _ := by
      have h := giant_ordered_product_fiber_second_moment 3 N
      simpa only [Nat.reduceMul, mul_assoc] using mul_le_mul_of_nonneg_left h (sq_nonneg (M/Z))

/-- A fixed logarithmic bound holds uniformly on translated intervals for
the collapsed coefficient vector of each two- or three-factor box. -/
theorem sourceComparisonTriple_translated_mean (σ D X : ℝ) (hσ : 0 ≤ σ) (hX : 1 ≤ X)
    (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ) (Z T ξ : ℝ)
    (hZ : 1 ≤ Z) (hT : 0 < T) (hTZ : T ≤ Z) (hZX : Z ≤ Real.exp (σ*X))
    (hc : ∀ v ∈ S, ‖c v‖ ≤ X^D) :
    (∫ t in Set.Icc (-T) T,
      ‖markedNaturalPolynomial (Ioc 0 ⌊8*Z⌋₊) (sourceComparisonTripleCoefficient S c Z) (t+ξ)‖^2) ≤
      576*Real.exp 1*(1+Real.log 8+σ)^9*X^(2*D+9) := by
  let N := ⌊8*Z⌋₊
  let Q := 1+Real.log 8+σ
  have hX0 : 0 < X := by linarith
  have hZ0 : 0 < Z := by linarith
  have hN1 : 1 ≤ N := (Nat.le_floor_iff (by positivity)).mpr (by norm_num; linarith)
  have hN0 : (0:ℝ) < N := by exact_mod_cast zero_lt_one.trans_le hN1
  have hN8 : (N:ℝ) ≤ 8*Z := Nat.floor_le (by positivity)
  have hlog0 : 0 ≤ 1+Real.log (N:ℝ) := by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ N by exact_mod_cast hN1)]
  have hlog : 1+Real.log (N:ℝ) ≤ Q*X := by
    have hz := (Real.log_le_iff_le_exp hZ0).mpr hZX
    have hn := Real.log_le_log hN0 hN8
    rw [Real.log_mul (by norm_num) hZ0.ne'] at hn
    dsimp [Q]
    nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 8)]
  have hm := markedNaturalPolynomial_translated_mean_square (Ioc 0 N) (N := N)
    Subset.rfl (sourceComparisonTripleCoefficient S c Z) ξ hT
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at hm
  have hs := sourceComparisonTripleCoefficient_square_mass S c N Z (X^D) hZ0 (by positivity) hc
  calc
    _ ≤ 8*Real.exp 1*(T+(N:ℝ))*((X^D/Z)^2*(N:ℝ)*(1+Real.log (N:ℝ))^(9:ℕ)) :=
      hm.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    _ ≤ 8*Real.exp 1*(9*Z)*((X^D/Z)^2*(8*Z)*(Q*X)^(9:ℕ)) := by
      have ht : T+(N:ℝ) ≤ 9*Z := by linarith
      gcongr
    _ = _ := by
      rw [Real.rpow_add hX0 (2*D) 9, show 2*D=D*2 by ring, Real.rpow_mul hX0.le,
        Real.rpow_two, show (9:ℝ)=(9:ℕ) by norm_num, Real.rpow_natCast]
      dsimp [Q]
      field_simp
      ring

end
end ArtinMatthews
