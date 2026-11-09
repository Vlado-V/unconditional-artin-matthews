module

public import ArtinMatthews.MarkedPhysicalCoordinateIndex
public import ArtinMatthews.MarkedPhysicalSharpTubeBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Count the actual coordinate, ordered marking and two-slot-copy
carrier at the original source exponents, with total exponent .73. -/
namespace ArtinMatthews
noncomputable section

def markedPhysicalSharpIndexCost (groups : ℕ) (K A : ℝ) : ℝ :=
  markedPhysicalSharpTubeCost K A+48*(groups:ℝ)

theorem markedPhysicalSharpIndexCost_nonneg (groups : ℕ) {K A : ℝ}
    (hK : 0 ≤ K) (hA : 0 ≤ A) : 0 ≤ markedPhysicalSharpIndexCost groups K A :=
  add_nonneg (markedPhysicalSharpTubeCost_nonneg hK hA) (by positivity)

theorem markedPhysicalLabelPath_exponent_sharp (groups : ℕ) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    2*(groups:ℝ)*(markedPadSlots x:ℝ)*((markedMemoryMomentLength x:ℝ)+1)*(Real.log x)^(1/5:ℝ) ≤
      16*(groups:ℝ)*(Real.log x)^(73/100:ℝ) := by
  have hL : 0 < Real.log x := by linarith
  have hm := markedPadSlots_pow_le 1 hlog
  simp only [pow_one,Nat.cast_one] at hm
  have hn := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hprod := mul_le_mul hm hn (by positivity) (by positivity)
  have hg := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2*(groups:ℝ)*(Real.log x)^(1/5:ℝ) by positivity)
  have he1 : (Real.log x)^(1/100:ℝ)*(Real.log x)^(1/2:ℝ)=(Real.log x)^(51/100:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  have he2 : (Real.log x)^(51/100:ℝ)*(Real.log x)^(1/5:ℝ)=(Real.log x)^(71/100:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  calc
    _ ≤ 2*(groups:ℝ)*(2*(Real.log x)^(1/100:ℝ))*(4*(Real.log x)^(1/2:ℝ))*(Real.log x)^(1/5:ℝ) := by
      nlinarith
    _ = 16*(groups:ℝ)*((Real.log x)^(1/100:ℝ)*(Real.log x)^(1/2:ℝ))*(Real.log x)^(1/5:ℝ) := by ring
    _ = 16*(groups:ℝ)*(Real.log x)^(71/100:ℝ) := by rw [he1,mul_assoc,he2]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (71/100:ℝ) ≤ 73/100)) (by positivity)

theorem markedPhysicalCopyPath_exponent_sharp (groups : ℕ) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    2*(groups:ℝ)*(markedPadSlots x:ℝ)^2*(markedMemoryMomentLength x:ℝ) ≤
      32*(groups:ℝ)*(Real.log x)^(73/100:ℝ) := by
  have hL : 0 < Real.log x := by linarith
  have hm := markedPadSlots_pow_le 2 hlog
  norm_num only [Nat.cast_ofNat] at hm
  have hn : (markedMemoryMomentLength x:ℝ) ≤ 4*(Real.log x)^(1/2:ℝ) := by
    linarith [(markedMemoryMomentLength_sqrt_bound hlog).1]
  have hprod := mul_le_mul hm hn (by positivity) (by positivity)
  have hg := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*(groups:ℝ) by positivity)
  have he : (Real.log x)^(2/100:ℝ)*(Real.log x)^(1/2:ℝ)=(Real.log x)^(13/25:ℝ) := by
    rw [← Real.rpow_add hL]
    norm_num
  calc
    _ ≤ 2*(groups:ℝ)*(4*(Real.log x)^(2/100:ℝ))*(4*(Real.log x)^(1/2:ℝ)) := by nlinarith
    _ = 32*(groups:ℝ)*((Real.log x)^(2/100:ℝ)*(Real.log x)^(1/2:ℝ)) := by ring
    _ = 32*(groups:ℝ)*(Real.log x)^(13/25:ℝ) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (13/25:ℝ) ≤ 73/100)) (by positivity)

theorem markedPhysicalCoordinateIndex_actual_card_sharp
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)
    {x K H A : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hHhi : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    (Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)
      (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H)):ℝ) ≤
      Real.exp (markedPhysicalSharpIndexCost (Fintype.card J) K A*(Real.log x)^(73/100:ℝ)) := by
  have hc := markedPhysicalCoordinateIndex_card_exp_bound e hlog he (markedPadSlots x)
    (markedMemoryMomentLength x) (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H)
  have hl := Real.exp_le_exp.mpr (markedPhysicalLabelPath_exponent_sharp (Fintype.card J) hlog)
  have ht := markedPhysicalMomentTube_path_sharp hlog hK hH hA hHhi
  have hs := Real.exp_le_exp.mpr (markedPhysicalCopyPath_exponent_sharp (Fintype.card J) hlog)
  apply hc.trans
  calc
    _ ≤ Real.exp (16*(Fintype.card J:ℝ)*(Real.log x)^(73/100:ℝ))*
        Real.exp (markedPhysicalSharpTubeCost K A*(Real.log x)^(73/100:ℝ))*
        Real.exp (32*(Fintype.card J:ℝ)*(Real.log x)^(73/100:ℝ)) :=
      mul_le_mul (mul_le_mul hl ht (by positivity) (Real.exp_nonneg _)) hs (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      unfold markedPhysicalSharpIndexCost
      ring

end
end ArtinMatthews
