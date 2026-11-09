module

public import ArtinMatthews.MarkedPhysicalBonferroniModulus
public import ArtinMatthews.MarkedPhysicalActualUsedBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The performed modulus at the actual moment/pad lengths satisfies the
proved root-count ceiling with the used-prime budget fully discharged. -/

noncomputable section
namespace ArtinMatthews

theorem markedPhysicalActualBonferroniModulus_bound
    {J : Type*} [Fintype J] (e : J → ℝ) {x : ℝ}
    (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x))
    (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \ markedPhysicalPathUsedPrimes Finset.univ a)
    (hc : T.card ≤ 2*markedPhysicalBonferroniDepth x+1) :
    (markedPhysicalBonferroniModulus Finset.univ a T:ℝ) ≤
      Real.exp ((16*(Fintype.card J:ℝ)+10)*(Real.log x)^(49/50:ℝ)) :=
  markedPhysicalBonferroniModulus_actual_bound e (by positivity) hlog he (by norm_num) Finset.univ a hT hc
    (markedPhysicalActualUsedProduct_bound e hlog he a)

end ArtinMatthews
