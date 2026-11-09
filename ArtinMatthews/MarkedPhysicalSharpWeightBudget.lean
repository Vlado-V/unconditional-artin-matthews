module

public import ArtinMatthews.MarkedPhysicalActualNormalizer
public import ArtinMatthews.MarkedPhysicalSharpLogBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The literal physical mass times the actual uniform coordinate-copy
bound is exp(C*log(x)^.73). The source Q=log(x)^A, moment length and
slot count are unchanged. The literal band normalizer supplies the kernel bound. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

def markedPhysicalSharpWeightCost (groups : ℕ) (etaBound psiBound Qexp : ℝ) : ℝ :=
  2*markedPhysicalBandInverseBound*(groups:ℝ)+
    4*(markedPhysicalActualEdgeBound groups etaBound psiBound+15*Qexp)

theorem markedPhysicalSharpWeightCost_nonneg (groups : ℕ) (etaBound : ℝ)
    {psiBound Qexp : ℝ} (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) :
    0 ≤ markedPhysicalSharpWeightCost groups etaBound psiBound Qexp := by
  have hc := markedPhysicalBandInverseBound_pos
  have he := markedPhysicalActualEdgeBound_nonneg groups (etaBound := etaBound) hpsi
  unfold markedPhysicalSharpWeightCost
  positivity

theorem markedPhysicalCoordinateWeight_actual_sharp
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,0 < e j)
    (etaBound psiBound Qexp : ℝ) (hpsi : 0 ≤ psiBound) (hQexp : 0 ≤ Qexp) :
    ∀ᶠ x : ℝ in atTop,
      markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) *
        (markedPhysicalCoordinateEdgeBound (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          etaBound psiBound * ((Real.log x)^Qexp)^3)^(markedMemoryMomentLength x) ≤
      Real.exp (markedPhysicalSharpWeightCost (Fintype.card J) etaBound psiBound Qexp *
        (Real.log x)^(73/100:ℝ)) := by
  filter_upwards [markedPhysicalActualNormalizer_bounds e he etaBound psiBound hpsi,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hn hlog
  let E := markedPhysicalActualEdgeBound (Fintype.card J) etaBound psiBound
  have hE : 0 ≤ E := markedPhysicalActualEdgeBound_nonneg _ (etaBound := etaBound) hpsi
  have hc : 0 ≤ markedPhysicalBandInverseBound := markedPhysicalBandInverseBound_pos.le
  have hL : 0 < Real.log x := by linarith
  have hQ0 : 0 ≤ ((Real.log x)^Qexp)^3 := by positivity
  have hM := markedPadSlots_pow_le 1 hlog
  simp only [pow_one,Nat.cast_one] at hM
  have hMr : (markedPadSlots x:ℝ) ≤ 2*(Real.log x)^(73/100:ℝ) := hM.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1/100:ℝ) ≤ 73/100)) (by norm_num))
  have hmass : markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) ≤
      Real.exp (2*markedPhysicalBandInverseBound*(Fintype.card J:ℝ)*(Real.log x)^(73/100:ℝ)) := by
    apply (hn.1 (markedPadSlots x)).2.trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hMr
      (show 0 ≤ markedPhysicalBandInverseBound*(Fintype.card J:ℝ) by positivity)
    nlinarith
  have hpow : ((Real.log x)^Qexp)^3=Real.exp (3*Qexp*Real.log (Real.log x)) := by
    rw [Real.rpow_def_of_pos hL,← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hEe : E ≤ Real.exp E := by linarith [Real.add_one_le_exp E]
  have hedge0 : 0 ≤ markedPhysicalCoordinateEdgeBound
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) etaBound psiBound := by
    unfold markedPhysicalCoordinateEdgeBound
    positivity
  have hbase : markedPhysicalCoordinateEdgeBound
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) etaBound psiBound*((Real.log x)^Qexp)^3 ≤
      Real.exp (E+3*Qexp*Real.log (Real.log x)) := by
    calc
      _ ≤ Real.exp E*((Real.log x)^Qexp)^3 :=
        mul_le_mul_of_nonneg_right (hn.2.trans hEe) hQ0
      _ = _ := by rw [hpow,← Real.exp_add]
  have hN := (markedMemoryMomentLength_sqrt_bound hlog).1
  have hN0 : (markedMemoryMomentLength x:ℝ) ≤ 4*(Real.log x)^(1/2:ℝ) := by linarith
  have hlogL : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlog
  have hlogLe := markedPhysical_log_log_sharp hlog
  have hcost : (markedMemoryMomentLength x:ℝ)*(E+3*Qexp*Real.log (Real.log x)) ≤
      4*(E+15*Qexp)*(Real.log x)^(73/100:ℝ) := by
    have he : E+3*Qexp*Real.log (Real.log x) ≤ (E+15*Qexp)*(Real.log x)^(23/100:ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left (Real.one_le_rpow hlog (by norm_num : (0:ℝ) ≤ 23/100)) hE
      have h2 := mul_le_mul_of_nonneg_left hlogLe (show 0 ≤ 3*Qexp by positivity)
      nlinarith
    calc
      _ ≤ (4*(Real.log x)^(1/2:ℝ))*((E+15*Qexp)*(Real.log x)^(23/100:ℝ)) :=
        mul_le_mul hN0 he (by positivity) (by positivity)
      _ = _ := by
        have hp : (Real.log x)^(1/2:ℝ)*(Real.log x)^(23/100:ℝ)=(Real.log x)^(73/100:ℝ) := by
          rw [← Real.rpow_add hL]
          norm_num
        nlinarith
  have hkernel : (markedPhysicalCoordinateEdgeBound
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) etaBound psiBound*((Real.log x)^Qexp)^3)^
        (markedMemoryMomentLength x) ≤
      Real.exp (4*(E+15*Qexp)*(Real.log x)^(73/100:ℝ)) := by
    apply (pow_le_pow_left₀ (mul_nonneg hedge0 hQ0) hbase (markedMemoryMomentLength x)).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hcost
  calc
    _ ≤ Real.exp (2*markedPhysicalBandInverseBound*(Fintype.card J:ℝ)*(Real.log x)^(73/100:ℝ))*
        Real.exp (4*(E+15*Qexp)*(Real.log x)^(73/100:ℝ)) :=
      mul_le_mul hmass hkernel (by positivity) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      unfold markedPhysicalSharpWeightCost
      dsimp only [E]
      ring

end
end ArtinMatthews
