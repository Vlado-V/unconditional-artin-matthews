module

public import ArtinMatthews.GiantComparisonMellinTail


set_option backward.privateInPublic true
@[expose] public section

/-! The retained comparison energy and its translated mean-square tail
combine with the exact normalization of the local Mellin inequality. -/
namespace ArtinMatthews
open Filter MeasureTheory Finset
open scoped BigOperators
noncomputable section

theorem giantComparisonMellinPolynomial_weighted_core_tail (S : Finset ℕ) {N : ℕ}
    (hS : S ⊆ Ioc 0 N) (a : ℕ → ℂ) {X L B : ℝ} (hX : 0 < X) (hL : 0 ≤ L) (n : ℕ)
    (hcore : (∫ t in Set.Icc (-(L*X)) (L*X), ‖giantComparisonMellinPolynomial S a t‖^2) ≤ B) :
    (∫ t : ℝ, markedMajorFourierWeight X (n+2) t * ‖giantComparisonMellinPolynomial S a t‖^2) ≤
      B + ((1+L)^n)⁻¹ *
        (markedMajorLocalMeanConstant * (8*Real.exp 1*(X+(N : ℝ))*∑ w ∈ S, ‖a w‖^2)) := by
  let M := giantComparisonMellinPolynomial S a
  let f := fun t : ℝ => markedMajorFourierWeight X (n+2) t * ‖M t‖^2
  let K := Set.Icc (-(L*X)) (L*X)
  have hSpos (w : ℕ) (hw : w ∈ S) : 0 < w := (mem_Ioc.mp (hS hw)).1
  have hM := giantComparisonMellinPolynomial_continuous S hSpos a
  have hi : Integrable f := by
    simpa only [f, sub_zero] using
      markedMajorLocalMean_integrable_higher M hM (∑ w ∈ S, ‖a w‖)
        (giantComparisonMellinPolynomial_norm_le S hSpos a) hX 0 (by omega : 2 ≤ n+2)
  have hf (t : ℝ) : 0 ≤ f t :=
    mul_nonneg (markedMajorFourierWeight_nonneg hX _ _) (sq_nonneg _)
  have hK : MeasurableSet K := measurableSet_Icc
  have hcore' : (∫ t in K, f t) ≤ B := by
    apply le_trans _ hcore
    apply setIntegral_mono_on hi.integrableOn (hM.norm.pow 2).integrableOn_Icc hK
    intro t _
    have hweight : markedMajorFourierWeight X (n+2) t ≤ 1 := by
      unfold markedMajorFourierWeight
      exact inv_le_one_of_one_le₀ (one_le_pow₀
        (le_add_of_nonneg_right (div_nonneg (abs_nonneg t) hX.le)))
    exact mul_le_of_le_one_left (sq_nonneg _) hweight
  have hsubset : Kᶜ ⊆ {t : ℝ | L*X ≤ |t|} := by
    intro t ht
    change L*X ≤ |t|
    apply le_of_not_gt
    intro h
    exact ht (abs_le.mp h.le)
  have htail := giantComparisonMellinPolynomial_weighted_tail S hS a hX hL n
  change (∫ t : ℝ, f t) ≤ _
  rw [← integral_add_compl hK hi]
  exact add_le_add hcore' ((setIntegral_mono_set hi.integrableOn (ae_of_all _ hf)
    (Filter.Eventually.of_forall hsubset)).trans htail)

theorem giantComparisonMellinPolynomial_weighted_log_bound (K D A : ℝ)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∃ n : ℕ, ∀ᶠ L : ℝ in atTop,
      ∀ (S : Finset ℕ) (N : ℕ), S ⊆ Ioc 0 N →
      ∀ (a : ℕ → ℂ) (X Y : ℝ), 0 < X → X ≤ Y → (N : ℝ) ≤ K*Y →
      (∑ w ∈ S, ‖a w‖^2) ≤ Y*L^D →
      (∫ t in Set.Icc (-(L*X)) (L*X), ‖giantComparisonMellinPolynomial S a t‖^2) ≤
        Y^2 * L^(-(A+1)) →
      (∫ t : ℝ, markedMajorFourierWeight X (n+2) t * ‖giantComparisonMellinPolynomial S a t‖^2) ≤
        Y^2 * L^(-A) := by
  obtain ⟨n,hn⟩ := exists_nat_ge (A+D+1)
  let C := markedMajorLocalMeanConstant * (8*Real.exp 1*(1+K))
  have hC : 0 ≤ C := mul_nonneg markedMajorLocalMeanConstant_pos.le (by positivity)
  refine ⟨n, ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (2*C))] with L hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hCL : 2*C ≤ L := (le_max_right _ _).trans hL
  intro S N hS a X Y hX hXY hN hmass hcore
  have hY : 0 < Y := hX.trans_le hXY
  have hInv : ((1+L)^n)⁻¹ ≤ L^(-(n : ℝ)) := by
    rw [Real.rpow_neg hLp.le, Real.rpow_natCast]
    exact inv_anti₀ (pow_pos hLp _) (pow_le_pow_left₀ hLp.le (by linarith) _)
  have hcost : markedMajorLocalMeanConstant * (8*Real.exp 1*(X+(N : ℝ))*∑ w ∈ S, ‖a w‖^2) ≤
      C*(Y^2*L^D) := by
    have hc := mul_le_mul (add_le_add hXY hN) hmass (sum_nonneg fun _ _ => sq_nonneg _)
      (by positivity : 0 ≤ Y+K*Y)
    calc
      _ ≤ (markedMajorLocalMeanConstant*(8*Real.exp 1))*((Y+K*Y)*(Y*L^D)) := by
        rw [show markedMajorLocalMeanConstant * (8*Real.exp 1*(X+(N : ℝ))*∑ w ∈ S, ‖a w‖^2) =
          (markedMajorLocalMeanConstant*(8*Real.exp 1))*((X+(N : ℝ))*(∑ w ∈ S, ‖a w‖^2)) by ring]
        exact mul_le_mul_of_nonneg_left hc (mul_nonneg markedMajorLocalMeanConstant_pos.le (by positivity))
      _ = _ := by dsimp [C]; ring
  have htail : ((1+L)^n)⁻¹ *
      (markedMajorLocalMeanConstant * (8*Real.exp 1*(X+(N : ℝ))*∑ w ∈ S, ‖a w‖^2)) ≤
      (Y^2*L^(-A))/2 := by
    calc
      _ ≤ L^(-(n : ℝ))*(C*(Y^2*L^D)) :=
        mul_le_mul hInv hcost (by positivity [markedMajorLocalMeanConstant_pos])
          (Real.rpow_nonneg hLp.le _)
      _ = C*Y^2*L^(D-(n : ℝ)) := by
        rw [sub_eq_add_neg, Real.rpow_add hLp]
        ring
      _ ≤ C*Y^2*L^(-(A+1)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by positivity)
      _ = (C/L)*(Y^2*L^(-A)) := by
        rw [show -(A+1) = -A+(-1) by ring, Real.rpow_add hLp, Real.rpow_neg_one]
        ring
      _ ≤ (1/2 : ℝ)*(Y^2*L^(-A)) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hLp).mpr (by linarith)) (by positivity)
      _ = _ := by ring
  have hsmall : Y^2 * L^(-(A+1)) ≤ (Y^2*L^(-A))/2 := by
    rw [show -(A+1) = -A+(-1) by ring, Real.rpow_add hLp, Real.rpow_neg_one, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by norm_num : (0:ℝ)<2) hL2) (by positivity)
  refine (giantComparisonMellinPolynomial_weighted_core_tail S hS a hX hLp.le n hcore).trans ?_
  linarith

end
end ArtinMatthews
