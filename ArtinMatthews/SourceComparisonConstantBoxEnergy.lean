module

public import ArtinMatthews.SourceComparisonBoxEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! High-time energy of the literal constant boxes, with all residue classes. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

theorem sourceComparisonConstantBox_high_energy
    (c C d a D E A : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hd : 0 < d) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ∀ {ι : Type*} (J : Finset ι) (divisor : ι → ℕ) (coeff : ι → ℂ)
        (P T U : ℝ) (M N : ℕ) (β : ℕ → ℂ),
        1 < P → c*X^(1/(10:ℝ)) ≤ Real.log P → Real.log P ≤ C*X →
        1 < T → T ≤ Real.exp (2*X) → T ≤ U →
        U ≤ (M:ℝ)+1 → (N:ℝ) ≤ 2*U →
        (∀ n ∈ Icc (M+1) N, ‖β n‖ ≤ X^D) →
        (∀ i ∈ J, 0 < divisor i ∧ Real.exp (d*X) ≤ U/divisor i) →
        (∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ)) ≤ X^E →
        (∑ n ∈ Icc (M+1) N, ‖(β n - markedMajorDivisorPolynomial J divisor coeff n)/U‖^2) ≤
          X^(-(A+2*a+2))/U →
        ∀ (q : ℕ) [NeZero q] (h : ZMod q), (q:ℝ) ≤ X^a →
          ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p ∈ S, (p:ℝ) ≤ 2*P) →
          (∫ t in sourceComparisonHighTimes T (X^B),
            ‖sourceComparisonConstantBox h S (Icc (M+1) N) β P U t‖^2) ≤ X^(-A) := by
  let R := A+2*a
  obtain ⟨B,hB,hbox⟩ := sourceComparisonHighTime_constant c C d a D E R hc hC hd ha hD hE
    (by dsimp [R]; positivity)
  refine ⟨B,hB,?_⟩
  filter_upwards [hbox, eventually_ge_atTop (1:ℝ)] with X hbox hX
  have hX0 : 0 < X := by linarith
  intro ι J divisor coeff P T U M N β hP hlo hhi hT hTU hTH hM hN hβ hdJ hmass herr
    q _ h hq S hS hScap
  let W := sourceComparisonHighTimes T (X^B)
  have hW : W ⊆ Set.Icc (-T) T := fun _ ht => ht.1
  let w (v z : ZMod q) := ZMod.stdAddChar (h*v*z)
  let f (v : ZMod q) (t : ℝ) :=
    markedPrimePolynomial (sourceComparisonResidueFiber S v) P (1:DirichletCharacter ℂ 1) 0 t *
      markedDyadicPolynomial (M+1) N U (fun n => β n*w v (n:ZMod q)) t
  have hf (v : ZMod q) : Continuous (f v) :=
    (markedPrimePolynomial_continuous _ _ _ _).mul (markedDyadicPolynomial_continuous _ _ _ _)
  have hsingle (v : ZMod q) : (∫ t in W, ‖f v t‖^2) ≤ X^(-R) := by
    let S₁ := sourceComparisonResidueFiber S v
    have hw (z : ZMod q) : ‖w v z‖ = 1 := giant_stdAddChar_norm _
    have hb (n : ℕ) (hn : n ∈ Icc (M+1) N) : ‖β n*w v (n:ZMod q)‖ ≤ X^D := by
      simpa only [norm_mul, hw, mul_one] using hβ n hn
    have he (n : ℕ) :
        ‖(β n*w v (n:ZMod q) -
          markedMajorDivisorPolynomial J divisor coeff n*w v (n:ZMod q))/U‖^2 =
          ‖(β n-markedMajorDivisorPolynomial J divisor coeff n)/U‖^2 := by
      rw [← sub_mul, norm_div, norm_mul, hw, mul_one, norm_div]
    have herror :
        (∑ n ∈ Icc (M+1) N, ‖(β n*w v (n:ZMod q) -
          markedMajorDivisorPolynomial J divisor coeff n*w v (n:ZMod q))/U‖^2) ≤
          X^(-(R+2))/U := by
      simp_rw [he]
      exact herr
    exact hbox J divisor coeff P T U M N (fun n => β n*w v (n:ZMod q)) hP hlo hhi hT hTU hTH
      hM hN hb hdJ hmass q (w v) hq (fun z => (hw z).le) herror 1 1 0 S₁
      (fun p hp => hS p (mem_filter.mp hp).1) (fun p hp => hScap p (mem_filter.mp hp).1)
  have houter := sourceComparison_finiteSum_energy (univ : Finset (ZMod q)) f hW
    (fun v _ => hf v) (fun v _ => hsingle v)
  simp only [card_univ, ZMod.card] at houter
  simp_rw [sourceComparisonConstantBox_factor h S (M+1) N β P U _
    (fun p hp => (hS p hp).pos) (Nat.succ_pos M)]
  change (∫ t in W, ‖∑ v : ZMod q, f v t‖^2) ≤ _
  apply houter.trans
  calc
    _ ≤ (X^a)^2*X^(-R) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hq 2) (by positivity)
    _ = X^(-A) := by
      rw [← Real.rpow_mul_natCast hX0.le, ← Real.rpow_add hX0]
      congr 1
      dsimp [R]
      push_cast
      ring

end
end ArtinMatthews
