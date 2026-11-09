module

public import ArtinMatthews.MarkedPhysicalPathUsedBudget
public import ArtinMatthews.MarkedPhysicalPathArrays
public import ArtinMatthews.MarkedMemoryOrphanParameterBounds
public import ArtinMatthews.MarkedRawRootArcGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The actual used-prime modulus budget follows directly from every
literal ordered label path. Repeated prime labels are retained by the
input and counted once by the actual union of used primes. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedPhysicalActualUsedProduct_bound
    {J : Type*} [Fintype J] (e : J → ℝ) {x : ℝ}
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) :
    ((∏ p∈markedPhysicalPathUsedPrimes Finset.univ a,p:ℕ):ℝ) ≤
      Real.exp (16*(Fintype.card J:ℝ)*(Real.log x)^(18/25:ℝ)) := by
  have hL : 0 < Real.log x := by linarith
  have hn := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hm := markedPadSlots_pow_le 1 hlog
  simp only [pow_one,Nat.cast_one,div_eq_mul_inv,one_mul] at hm
  have hNM := mul_le_mul hn hm (Nat.cast_nonneg _) (by positivity)
  have heq : (Real.log x)^(1/2:ℝ)*(Real.log x)^(1/100:ℝ)=(Real.log x)^(51/100:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hnm : ((markedMemoryMomentLength x:ℝ)+1)*(markedPadSlots x:ℝ) ≤
      8*(Real.log x)^(51/100:ℝ) := by nlinarith
  have hprime : (Real.log x)^(51/100:ℝ)*(Real.log x)^(1/5:ℝ)=(Real.log x)^(71/100:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have hinc : (Real.log x)^(71/100:ℝ) ≤ (Real.log x)^(18/25:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hcost : ((markedMemoryMomentLength x:ℝ)+1)*(Fintype.card J:ℝ)*(markedPadSlots x:ℝ)*
      (2*(Real.log x)^(1/5:ℝ)) ≤ 16*(Fintype.card J:ℝ)*(Real.log x)^(18/25:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hnm
      (show 0 ≤ 2*(Fintype.card J:ℝ)*(Real.log x)^(1/5:ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hinc (show 0 ≤ 16*(Fintype.card J:ℝ) by positivity)
    nlinarith
  have hprod := markedPhysicalPathUsedPrimes_prod_le_exp Finset.univ a (2*(Real.log x)^(1/5:ℝ))
    (by positivity) (fun j p hp => markedRootArc_band_prime_le hlog (he j) hp)
  have hp : ((∏ p∈markedPhysicalPathUsedPrimes Finset.univ a,p:ℕ):ℝ) ≤
      Real.exp (((markedMemoryMomentLength x:ℝ)+1)*(Fintype.card J:ℝ)*(markedPadSlots x:ℝ)*
        (2*(Real.log x)^(1/5:ℝ))) := by
    simpa only [Nat.cast_prod,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hprod
  exact hp.trans (Real.exp_le_exp.mpr hcost)

end
end ArtinMatthews
