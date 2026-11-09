module

public import ArtinMatthews.MarkedProgressionDivisorMoment
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual representations in the two factor intervals. The product
bound cuts off the divisor moment, while the original quotient range is
retained in the weighted pairing. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def markedTypeIIProductFiber (M N : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (M ×ˢ N).filter (fun v => v.1*v.2 = k)

def markedTypeIIQuotientCoefficient (M N : Finset ℕ) (α β : ℕ → ℂ) (a h : ℕ) : ℂ :=
  ∑ v ∈ markedTypeIIProductFiber M N (1+a*h), α v.1 * β v.2

theorem markedTypeIIProductFiber_card_le (M N : Finset ℕ) {k : ℕ} (hk : 0 < k) :
    (markedTypeIIProductFiber M N k).card ≤ k.divisors.card := by
  apply card_le_card_of_injOn Prod.fst
  · intro v hv
    have he := (mem_filter.mp hv).2
    exact Nat.mem_divisors.mpr ⟨⟨v.2,he.symm⟩,hk.ne'⟩
  · intro v hv w hw he
    have hvk := (mem_filter.mp hv).2
    have hwk := (mem_filter.mp hw).2
    have hv0 : 0 < v.1 := by
      by_contra! h
      have hz := Nat.eq_zero_of_le_zero h
      simp only [hz,zero_mul] at hvk
      exact hk.ne' hvk.symm
    refine Prod.ext he (Nat.eq_of_mul_eq_mul_left hv0 ?_)
    rw [hvk,he,hwk]

theorem markedTypeIIProductFiber_empty_of_lt (M N : Finset ℕ) {X k : ℕ}
    (hMN : ∀ v ∈ M×ˢN, v.1*v.2 ≤ X) (hk : X < k) :
    markedTypeIIProductFiber M N k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hbox,he⟩ := mem_filter.mp hv
  exact hk.not_ge (he ▸ hMN v hbox)

theorem markedTypeIIQuotientCoefficient_norm_le (M N : Finset ℕ) (α β : ℕ → ℂ)
    {A B : ℝ} (hA : 0 ≤ A) (hα : ∀ m ∈ M, ‖α m‖ ≤ A) (hβ : ∀ n ∈ N, ‖β n‖ ≤ B)
    (a h : ℕ) :
    ‖markedTypeIIQuotientCoefficient M N α β a h‖ ≤
      ((markedTypeIIProductFiber M N (1+a*h)).card:ℝ)*(A*B) := by
  unfold markedTypeIIQuotientCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ v ∈ markedTypeIIProductFiber M N (1+a*h), A*B := by
      apply sum_le_sum
      intro v hv
      obtain ⟨hm,hn⟩ := mem_product.mp (mem_filter.mp hv).1
      rw [norm_mul]
      exact mul_le_mul (hα _ hm) (hβ _ hn) (norm_nonneg _) hA
    _ = _ := by simp only [sum_const,nsmul_eq_mul]

theorem markedTypeIIQuotientCoefficient_square_le (M N H : Finset ℕ) (α β : ℕ → ℂ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ m ∈ M, ‖α m‖ ≤ A) (hβ : ∀ n ∈ N, ‖β n‖ ≤ B)
    {a X : ℕ} (ha : 0 < a) (haX : a^4 ≤ X)
    (hMN : ∀ v ∈ M×ˢN, v.1*v.2 ≤ X) :
    (∑ h ∈ H, ‖markedTypeIIQuotientCoefficient M N α β a h‖^2) ≤
      (A*B)^2 * (8*(X:ℝ)/a*(1+Real.log (X:ℝ))^3) := by
  let H' := H.filter (fun h => 1+a*h ≤ X)
  have hcut : ∀ h ∈ H', 1+a*h ≤ X := fun _ hh => (mem_filter.mp hh).2
  have hnorm (h : ℕ) :
      ‖markedTypeIIQuotientCoefficient M N α β a h‖ ≤
        ((1+a*h).divisors.card:ℝ)*(A*B) :=
    (markedTypeIIQuotientCoefficient_norm_le M N α β hA hα hβ a h).trans
      (mul_le_mul_of_nonneg_right
        (by exact_mod_cast markedTypeIIProductFiber_card_le M N (by omega : 0 < 1+a*h))
        (mul_nonneg hA hB))
  calc
    _ = ∑ h ∈ H', ‖markedTypeIIQuotientCoefficient M N α β a h‖^2 := by
      symm
      apply sum_subset (filter_subset _ _)
      intro h hh hn
      have hk : X < 1+a*h := lt_of_not_ge (fun hl => hn (mem_filter.mpr ⟨hh,hl⟩))
      simp only [markedTypeIIQuotientCoefficient,markedTypeIIProductFiber_empty_of_lt M N hMN hk,
        sum_empty,norm_zero,zero_pow two_ne_zero]
    _ ≤ ∑ h ∈ H', (A*B)^2*((1+a*h).divisors.card:ℝ)^2 := by
      apply sum_le_sum
      intro h _
      calc
        _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) (hnorm h) 2
        _ = _ := by ring
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (marked_progression_shifted_divisor_square_le ha haX H' hcut) (sq_nonneg _)

theorem markedTypeII_common_quotient_pair_norm_le (M N H : Finset ℕ)
    (α β : ℕ → ℂ) {A B Y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hY : 0 < Y)
    (hα : ∀ m ∈ M, ‖α m‖ ≤ A) (hβ : ∀ n ∈ N, ‖β n‖ ≤ B)
    {a b X : ℕ} (haY : Y ≤ (a:ℝ)) (hbY : Y ≤ (b:ℝ)) (haX : a^4 ≤ X) (hbX : b^4 ≤ X)
    (hMN : ∀ v ∈ M×ˢN, v.1*v.2 ≤ X) :
    ‖∑ h ∈ H, markedTypeIIQuotientCoefficient M N α β a h *
        star (markedTypeIIQuotientCoefficient M N α β b h)‖ ≤
      (A*B)^2 * (8*(X:ℝ)/Y*(1+Real.log (X:ℝ))^3) := by
  let C := (A*B)^2 * (8*(X:ℝ)/Y*(1+Real.log (X:ℝ))^3)
  have hX : 1 ≤ X := (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ (by exact_mod_cast (hY.trans_le haY).ne' : a ≠ 0))).trans haX
  have hlog : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hsq {l : ℕ} (hlY : Y ≤ (l:ℝ)) (hlX : l^4 ≤ X) :
      (∑ h ∈ H, ‖markedTypeIIQuotientCoefficient M N α β l h‖^2) ≤ C := by
    have hl : 0 < l := by exact_mod_cast hY.trans_le hlY
    refine (markedTypeIIQuotientCoefficient_square_le M N H α β hA hB hα hβ hl hlX hMN).trans ?_
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) hY hlY)
    positivity
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul,norm_star]
  calc
    _ ≤ ∑ h ∈ H, (‖markedTypeIIQuotientCoefficient M N α β a h‖^2 +
        ‖markedTypeIIQuotientCoefficient M N α β b h‖^2)/2 := by
      apply sum_le_sum
      intro h _
      nlinarith [sq_nonneg (‖markedTypeIIQuotientCoefficient M N α β a h‖ -
        ‖markedTypeIIQuotientCoefficient M N α β b h‖)]
    _ ≤ C := by
      simp only [div_eq_mul_inv,← sum_mul,sum_add_distrib]
      linarith [hsq haY haX,hsq hbY hbX]

end
end ArtinMatthews
