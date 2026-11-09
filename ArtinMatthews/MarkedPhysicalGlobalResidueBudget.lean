module

public import ArtinMatthews.MarkedPhysicalSelectedResidueBudget
public import ArtinMatthews.MarkedPhysicalSharpIndexBudget
public import ArtinMatthews.MarkedPhysicalActualNormalizer


set_option backward.privateInPublic true
@[expose] public section

/-! The complete actual coordinate, selected-subset and matrix-residue
enumeration, including the original physical mass, has a .99 budget. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

def markedPhysicalGlobalSelectedResidueCount {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x K H : ℝ) : ℝ :=
  ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
    (markedPadSlots x) (markedMemoryMomentLength x)
    (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H),
    markedPhysicalSelectedResidueCount e x i.1 (2*markedPhysicalBonferroniDepth x+1)

def markedPhysicalGlobalResidueCost (groups : ℕ) (K A : ℝ) : ℝ :=
  markedPhysicalSharpIndexCost groups K A+64*(groups:ℝ)+56+2*markedPhysicalBandInverseBound*(groups:ℝ)

theorem markedPhysicalGlobalSelectedResidueCount_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x K H : ℝ) : 0 ≤ markedPhysicalGlobalSelectedResidueCount e x K H := by
  apply Finset.sum_nonneg
  intro i _
  unfold markedPhysicalSelectedResidueCount
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem markedPhysicalGlobalSelectedResidueCount_bound {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {x K H A : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hA : 0 ≤ A) (hscale : H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ))) :
    markedPhysicalGlobalSelectedResidueCount e x K H ≤ 
      Real.exp ((markedPhysicalSharpIndexCost (Fintype.card J) K A+64*(Fintype.card J:ℝ)+56)*
        (Real.log x)^(99/100:ℝ)) := by
  have hi := markedPhysicalCoordinateIndex_actual_card_sharp e hlog he hK hH hA hscale
  have hc : markedPhysicalGlobalSelectedResidueCount e x K H ≤ 
      (Fintype.card (MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x)
        (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H)):ℝ)*
      Real.exp ((64*(Fintype.card J:ℝ)+56)*(Real.log x)^(49/50:ℝ)) := by
    calc
      _ ≤ ∑ _i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x)
          (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K H),
          Real.exp ((64*(Fintype.card J:ℝ)+56)*(Real.log x)^(49/50:ℝ)) :=
        Finset.sum_le_sum (fun i _ => markedPhysicalSelectedResidueCount_log_bound e hlog he i.1)
      _ = _ := by simp
  apply (hc.trans (mul_le_mul_of_nonneg_right hi (Real.exp_nonneg _))).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ha := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (73/100:ℝ) ≤ 99/100))
    (markedPhysicalSharpIndexCost_nonneg (Fintype.card J) hK hA)
  have hb := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (49/50:ℝ) ≤ 99/100))
    (show 0 ≤ 64*(Fintype.card J:ℝ)+56 by positivity)
  nlinarith

theorem markedPhysicalGlobalSelectedResidue_mass_bound {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,0<e j) (he1 : ∀ j,e j ≤ (1/5:ℝ)) :
    ∀ᶠ x : ℝ in atTop,∀ (K H A : ℝ),0 ≤ K → 0 ≤ H → 0 ≤ A →
      H ≤ Real.exp (A*(Real.log x)^(21/100:ℝ)) →
      markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
        markedPhysicalGlobalSelectedResidueCount e x K H ≤ 
      Real.exp (markedPhysicalGlobalResidueCost (Fintype.card J) K A*(Real.log x)^(99/100:ℝ)) := by
  filter_upwards [markedPhysicalActualNormalizer_bounds e he0 0 0 (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hm hlog
  intro K H A hK hH hA hscale
  have hb := (hm.1 (markedPadSlots x)).2
  have hM := markedPadSlots_pow_le 1 hlog
  simp only [pow_one,Nat.cast_one] at hM
  have hpow := Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1/100:ℝ) ≤ 99/100)
  have hmass : markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) ≤ 
      Real.exp ((2*markedPhysicalBandInverseBound*(Fintype.card J:ℝ))*(Real.log x)^(99/100:ℝ)) := by
    apply hb.trans
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ markedPhysicalBandInverseBound*(Fintype.card J:ℝ) := by
      exact mul_nonneg markedPhysicalBandInverseBound_pos.le (Nat.cast_nonneg _)
    have hh := mul_le_mul_of_nonneg_left (hM.trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 2))) hc
    nlinarith
  calc
    _ ≤ Real.exp ((2*markedPhysicalBandInverseBound*(Fintype.card J:ℝ))*(Real.log x)^(99/100:ℝ))*
        Real.exp ((markedPhysicalSharpIndexCost (Fintype.card J) K A+64*(Fintype.card J:ℝ)+56)*
          (Real.log x)^(99/100:ℝ)) :=
      mul_le_mul hmass (markedPhysicalGlobalSelectedResidueCount_bound e hlog he1 hK hH hA hscale)
        (markedPhysicalGlobalSelectedResidueCount_nonneg e x K H) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold markedPhysicalGlobalResidueCost; ring

end
end ArtinMatthews
