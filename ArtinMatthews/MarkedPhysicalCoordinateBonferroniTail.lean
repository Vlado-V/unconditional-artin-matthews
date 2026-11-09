module

public import ArtinMatthews.MarkedPhysicalBonferroniExpectedTail
public import ArtinMatthews.MarkedPhysicalSharpTotalBudget
public import ArtinMatthews.MarkedPhysicalCoordinateGoodVolume
public import ArtinMatthews.MarkedPhysicalCoordinateCapacityGlobal


set_option backward.privateInPublic true
@[expose] public section

/-! The actual selected-residue Bonferroni tail is summed over the full
physical coordinate carrier, with its original mass, coefficients and
good volumes. Every finite carrier and coefficient cost is discharged. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Classical
noncomputable section

def markedPhysicalCoordinateIndexTailMean {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x q : ℝ) {B : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B) (hB : 1≤B) : ℝ :=
  markedPhysicalBonferroniTailMean (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    Finset.univ i.1 (markedMemoryVisitQ q (markedMemoryMomentLength x))
    (markedPhysicalCoordinateIndexPath i.2.1)
    (markedPhysicalCoordinateIndexPath_primitive hB i.2.1) (2*markedPhysicalBonferroniDepth x+1)

def markedPhysicalCoordinateBonferroniTailMass {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U W : ℝ) (B : ℕ) (hB : 1≤B) : ℝ :=
  markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B,
      ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖*
      markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB*
      markedPhysicalCoordinateIndexTailMean e x q i hB

theorem markedPhysicalCoordinateIndexTailMean_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) {B : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B) (hB : 1≤B) :
    0 ≤ markedPhysicalCoordinateIndexTailMean e x q i hB :=
  markedPhysicalBonferroniTailMean_nonneg _ Finset.univ i.1
    (markedMemoryVisitQ q (markedMemoryMomentLength x))
    (fun v _ => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 _ v)
    (markedPhysicalCoordinateIndexPath i.2.1)
    (markedPhysicalCoordinateIndexPath_primitive hB i.2.1) _

theorem markedPhysicalCoordinateBonferroniTailMass_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q U W : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (B : ℕ) (hB : 1≤B) :
    0 ≤ markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U W B hB := by
  apply mul_nonneg
  · apply markedPhysicalMass_nonneg
    intro j
    unfold bandReciprocalMass
    positivity
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (norm_nonneg _)
      (markedPhysicalCoordinateIndexGoodVolume_bounds e x d₀ Y U W i hB).1)
      (markedPhysicalCoordinateIndexTailMean_nonneg e x q hq0 hq1 i hB)

theorem markedPhysicalCoordinateBonferroniTailMass_moment_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he0 : ∀ j,0<e j) (he1 : ∀ j,e j≤(1/5:ℝ)) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (K Hexp etaBound psiBound Qexp G : ℝ)
    (hK : 0≤K) (hHexp : 0≤Hexp) (heta : 0≤etaBound) (hpsi : 0≤psiBound)
    (hQexp : 0≤Qexp) (hG : 0≤G) (hη : ∀ t,‖η t‖≤etaBound) (hψ : ∀ t,‖ψ t‖≤psiBound) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ) (hd₀ : 0≤d₀) (hY : 1≤Y),
      d₀*Y≤Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) → ∀ (q U W : ℝ),0≤q → q≤1 →
      markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y ((Real.log x)^Qexp) q U W
        (markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y))
        (markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀ (zero_le_one.trans hY)))≤
          (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  let C := markedPhysicalSharpTotalCost (Fintype.card J) K Hexp etaBound psiBound Qexp
  filter_upwards [markedPhysicalCoordinateCoefficient_actual_total_sharp e he0 he1 ψ η K Hexp
      etaBound psiBound Qexp hK hHexp heta hpsi hQexp hη hψ,
    markedPhysicalActualVisitQTailMean_log_saving e he0 he1 hinj (C+15) G hG,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hc ht hlog
  intro d₀ Y hd₀ hY hscale q U W hq0 hq1
  let B := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hB : 1≤B := markedPhysicalMomentTubeRadius_ge_one _ hK (mul_nonneg hd₀ (zero_le_one.trans hY))
  let V := fun j => bandReciprocalMass (markedLogPowerBand (e j) x)
  let c := fun i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B =>
    ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y ((Real.log x)^Qexp) i‖
  let v := fun i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) B =>
    markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U W i hB
  let E := Real.exp ((C+15)*(Real.log x)^(73/100:ℝ))
  let P := (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ))
  have hE : 0<E := Real.exp_pos _
  have hP : 0≤P := Real.rpow_nonneg (zero_le_one.trans hlog) _
  have htail (i) : markedPhysicalCoordinateIndexTailMean e x q i hB≤P/E := by
    apply (le_div_iff₀ hE).mpr
    have hh := ht i.1 q hq0 hq1 (markedPhysicalCoordinateIndexPath i.2.1)
      (markedPhysicalCoordinateIndexPath_primitive hB i.2.1)
    change E*markedPhysicalCoordinateIndexTailMean e x q i hB≤P at hh
    exact (mul_comm _ _).trans_le hh
  have hV : ∀ j,0≤V j := by intro j; unfold V bandReciprocalMass; positivity
  have hm : 0 ≤ markedPhysicalMass V (markedPadSlots x) := markedPhysicalMass_nonneg V _ hV
  have hsum : (∑ i,c i*v i*markedPhysicalCoordinateIndexTailMean e x q i hB)≤
      (15*(∑ i,c i))*(P/E) := by
    calc
      _ ≤ ∑ i,(15*c i)*(P/E) := by
        apply Finset.sum_le_sum
        intro i _
        have hv := markedPhysicalCoordinateIndexGoodVolume_bounds e x d₀ Y U W i hB
        have hc0 : 0≤c i := norm_nonneg _
        exact (mul_le_mul_of_nonneg_left (htail i) (mul_nonneg hc0 hv.1)).trans
          (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hv.2 hc0])
            (div_nonneg hP hE.le))
      _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]
  have hmass := hc d₀ Y hd₀ hY hscale
  change markedPhysicalMass V (markedPadSlots x)*(∑ i,c i)≤Real.exp (C*(Real.log x)^(73/100:ℝ)) at hmass
  have h15 : (15:ℝ)≤Real.exp (15*(Real.log x)^(73/100:ℝ)) := by
    have hp := Real.one_le_rpow hlog (by norm_num : (0:ℝ)≤73/100)
    linarith [Real.add_one_le_exp (15*(Real.log x)^(73/100:ℝ))]
  have hnum : 15*(markedPhysicalMass V (markedPadSlots x)*(∑ i,c i))≤E := by
    calc
      _ ≤ 15*Real.exp (C*(Real.log x)^(73/100:ℝ)) := mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ ≤ Real.exp (15*(Real.log x)^(73/100:ℝ))*Real.exp (C*(Real.log x)^(73/100:ℝ)) :=
        mul_le_mul_of_nonneg_right h15 (Real.exp_nonneg _)
      _ = E := by unfold E; rw [← Real.exp_add]; congr 1; ring
  change markedPhysicalMass V (markedPadSlots x)*
    (∑ i,c i*v i*markedPhysicalCoordinateIndexTailMean e x q i hB)≤P
  calc
    _ ≤ markedPhysicalMass V (markedPadSlots x)*((15*(∑ i,c i))*(P/E)) :=
      mul_le_mul_of_nonneg_left hsum hm
    _ = (15*(markedPhysicalMass V (markedPadSlots x)*(∑ i,c i)))*(P/E) := by ring
    _ ≤ E*(P/E) := mul_le_mul_of_nonneg_right hnum (div_nonneg hP hE.le)
    _ = P := mul_div_cancel₀ P hE.ne'

end
end ArtinMatthews
