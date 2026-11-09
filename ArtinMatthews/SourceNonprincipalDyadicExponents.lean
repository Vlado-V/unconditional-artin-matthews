module

public import ArtinMatthews.SourceContinuedPoissonDyadicRightBounds


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed summable dyadic factor is paid before comparing exponents.
This handles both finite ranges and the infinite far range with the
same exact power loss. -/
namespace ArtinMatthews.SourceEulerAssembly
open VaryingKummerAnalytic
noncomputable section

def sourceDyadicLoss : ℝ := 1/100000

def sourceNonprincipalTargetExponent : ℝ := 7/15-1/2500

def sourceNonprincipalDyadicWeight (j : ℕ) : ℝ := ((2 : ℝ)^j)^(-sourceDyadicLoss)

theorem sourceNonprincipalDyadicWeight_nonneg (j : ℕ) : 0 ≤ sourceNonprincipalDyadicWeight j :=
  Real.rpow_nonneg (by positivity) _

theorem sourceNonprincipalDyadicWeight_summable : Summable sourceNonprincipalDyadicWeight := by
  have h0 : 0 ≤ (2 : ℝ)^(-sourceDyadicLoss) := Real.rpow_nonneg (by norm_num) _
  have h1 : (2 : ℝ)^(-sourceDyadicLoss) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num [sourceDyadicLoss])
  apply (summable_geometric_of_lt_one h0 h1).congr
  intro j
  symm
  unfold sourceNonprincipalDyadicWeight
  calc
    _ = (2 : ℝ)^((j : ℝ)*(-sourceDyadicLoss)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    _ = _ := by rw [mul_comm, Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]

private theorem sourceDyadic_power_reduce {Z U a b t p : ℝ} (hZ : 1 ≤ Z) (hU : 0 < U)
    (hpow : U^(b+sourceDyadicLoss) ≤ (Z^t)^(b+sourceDyadicLoss))
    (hExp : a+t*(b+sourceDyadicLoss) ≤ p) :
    Z^a*U^b ≤ Z^p*U^(-sourceDyadicLoss) := by
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ
  calc
    _ = (Z^a*U^(b+sourceDyadicLoss))*U^(-sourceDyadicLoss) := by
      rw [mul_assoc, ← Real.rpow_add hU, add_neg_cancel_right]
    _ ≤ (Z^a*(Z^t)^(b+sourceDyadicLoss))*U^(-sourceDyadicLoss) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hZ₀.le _)) (Real.rpow_nonneg hU.le _)
    _ = Z^(a+t*(b+sourceDyadicLoss))*U^(-sourceDyadicLoss) := by
      rw [← Real.rpow_mul hZ₀.le, ← Real.rpow_add hZ₀]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hZ hExp) (Real.rpow_nonneg hU.le _)

theorem sourceNonprincipalDyadic_small_power {Z U : ℝ} (hZ : 1 ≤ Z) (hU : 0 < U)
    (hsmall : U ≤ Z^(9/100 : ℝ)) :
    Z^(sourceContourExponent principalProbeSigma (3/1000) (2/5))*
      U^(1/10+sourceDyadicLoss+(1+sourceDyadicLoss)) ≤ Z^sourceNonprincipalTargetExponent*U^(-sourceDyadicLoss) := by
  apply sourceDyadic_power_reduce hZ hU (Real.rpow_le_rpow hU.le hsmall (by norm_num [sourceDyadicLoss]))
  norm_num [sourceContourExponent, principalProbeSigma, sourceDyadicLoss, sourceNonprincipalTargetExponent]

theorem sourceNonprincipalDyadic_exception_power {Z U : ℝ} (hZ : 1 ≤ Z) (hU : 0 < U)
    (hsmall : U ≤ Z^(10001/100000 : ℝ)) :
    Z^(sourceContourExponent principalProbeSigma (3/1000) (2/5))*
      U^(1/10+sourceDyadicLoss+1/2) ≤ Z^sourceNonprincipalTargetExponent*U^(-sourceDyadicLoss) := by
  apply sourceDyadic_power_reduce hZ hU (Real.rpow_le_rpow hU.le hsmall (by norm_num [sourceDyadicLoss]))
  norm_num [sourceContourExponent, principalProbeSigma, sourceDyadicLoss, sourceNonprincipalTargetExponent]

theorem sourceNonprincipalDyadic_good_center_power {Z U : ℝ} (hZ : 1 ≤ Z) (hU : 0 < U)
    (hsmall : U ≤ Z^(10001/100000 : ℝ)) :
    Z^(sourceContourExponent (499/500) (3/1000) (2/5))*
      U^(1/10+sourceDyadicLoss+(1+sourceDyadicLoss)) ≤ Z^sourceNonprincipalTargetExponent*U^(-sourceDyadicLoss) := by
  apply sourceDyadic_power_reduce hZ hU (Real.rpow_le_rpow hU.le hsmall (by norm_num [sourceDyadicLoss]))
  norm_num [sourceContourExponent, sourceDyadicLoss, sourceNonprincipalTargetExponent]

theorem sourceNonprincipalDyadic_good_error_power {Z U A : ℝ} (hZ : 1 ≤ Z) (hU : 0 < U)
    (hlarge : Z^(9/100 : ℝ) ≤ U) (hA : 2 ≤ A) :
    Z^(sourceContourExponent principalProbeSigma (3/1000) (2/5))*
      U^(1/10+sourceDyadicLoss-A+(1+sourceDyadicLoss)) ≤ Z^sourceNonprincipalTargetExponent*U^(-sourceDyadicLoss) := by
  apply sourceDyadic_power_reduce hZ hU (Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _) hlarge (by unfold sourceDyadicLoss; linarith))
  unfold sourceContourExponent principalProbeSigma sourceDyadicLoss sourceNonprincipalTargetExponent
  linarith

theorem sourceNonprincipalDyadic_far_power {Z U : ℝ} (hZ : 1 ≤ Z) (hU : 0 < U)
    (hlarge : Z^(10001/100000 : ℝ) ≤ U) :
    Z^(sourceContourExponent 4 4 350000)*U^(sourceDyadicLoss-350000+(1+sourceDyadicLoss)) ≤
      Z^sourceNonprincipalTargetExponent*U^(-sourceDyadicLoss) := by
  apply sourceDyadic_power_reduce hZ hU (Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _) hlarge (by norm_num [sourceDyadicLoss]))
  norm_num [sourceContourExponent, sourceDyadicLoss, sourceNonprincipalTargetExponent]

end
end ArtinMatthews.SourceEulerAssembly
