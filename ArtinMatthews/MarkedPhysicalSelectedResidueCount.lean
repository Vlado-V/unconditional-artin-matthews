module

public import ArtinMatthews.MarkedPhysicalActualBonferroniModulus
public import ArtinMatthews.MarkedPhysicalResidueBudget
public import ArtinMatthews.MarkedProgressionCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Count the literal selected-prime moduli and all their matrix residue
classes. Each summand retains its own performed modulus. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalSelectedResidueCount {J : Type*} [Fintype J]
    (e : J → ℝ) (x : ℝ)
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1),
    ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
      markedPhysicalPathUsedPrimes Finset.univ a).powersetCard j,
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ a T))):ℝ)

theorem markedPhysicalSelectedMatrixClass_bound {J : Type*} [Fintype J]
    (e : J → ℝ) {x : ℝ} (hlog : 1≤Real.log x) (he : ∀ j,e j≤(1/5:ℝ))
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) (T : Finset ℕ)
    (hT : T⊆markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
      markedPhysicalPathUsedPrimes Finset.univ a)
    (hc : T.card≤2*markedPhysicalBonferroniDepth x+1) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
      (ZMod (markedPhysicalBonferroniModulus Finset.univ a T))):ℝ)≤
      Real.exp ((64*(Fintype.card J:ℝ)+40)*(Real.log x)^(49/50:ℝ)) := by
  have hprime : ∀ j p,p∈markedLogPowerBand (e j) x → p.Prime :=
    fun _ _ hp => (mem_markedLogPowerBand.mp hp).1
  let : NeZero (markedPhysicalBonferroniModulus Finset.univ a T) :=
    ⟨(markedPhysicalBonferroniModulus_pos hprime Finset.univ a
      (fun p hp => (Finset.mem_sdiff.mp (hT hp)).1)).ne'⟩
  have hm := markedPhysicalActualBonferroniModulus_bound e hlog he a T hT hc
  calc
    _ ≤ (markedPhysicalBonferroniModulus Finset.univ a T:ℝ)^4 := markedPhysical_SL_card_bound _
    _ ≤ (Real.exp ((16*(Fintype.card J:ℝ)+10)*(Real.log x)^(49/50:ℝ)))^4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hm 4
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem markedPhysicalSelectedResidueCount_finite_bound {J : Type*} [Fintype J]
    (e : J → ℝ) {x : ℝ} (hlog : 1≤Real.log x) (he : ∀ j,e j≤(1/5:ℝ))
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) (k : ℕ)
    (hk : k≤2*markedPhysicalBonferroniDepth x+1) :
    markedPhysicalSelectedResidueCount e x a k≤
      Real.exp ((64*(Fintype.card J:ℝ)+40)*(Real.log x)^(49/50:ℝ))*
        ((k+1:ℕ):ℝ)*(max 1 (((markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
          markedPhysicalPathUsedPrimes Finset.univ a).card:ℝ)))^k := by
  let P := markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
    markedPhysicalPathUsedPrimes Finset.univ a
  let E := Real.exp ((64*(Fintype.card J:ℝ)+40)*(Real.log x)^(49/50:ℝ))
  have hcount : (∑ j ∈ Finset.range (k+1),∑ _T ∈ P.powersetCard j,(1:ℝ))≤
      ((k+1:ℕ):ℝ)*(max 1 (P.card:ℝ))^k := by
    simpa only [one_pow,mul_one,abs_pow,abs_neg,abs_one] using
      (marked_truncation_coefficient_mass_le P k (θ := 1) (by norm_num) le_rfl)
  have heach (j : ℕ) (hj : j∈Finset.range (k+1)) (T : Finset ℕ) (hT : T∈P.powersetCard j) :
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ a T))):ℝ)≤E := by
    have ht := Finset.mem_powersetCard.mp hT
    exact markedPhysicalSelectedMatrixClass_bound e hlog he a T ht.1
      (ht.2.le.trans ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hk))
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1),∑ _T ∈ P.powersetCard j,E := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum (fun T hT => heach j hj T hT)
    _ = E*(∑ j ∈ Finset.range (k+1),∑ _T ∈ P.powersetCard j,(1:ℝ)) := by
      simp only [Finset.mul_sum,mul_one]
    _ ≤ E*(((k+1:ℕ):ℝ)*(max 1 (P.card:ℝ))^k) :=
      mul_le_mul_of_nonneg_left hcount (Real.exp_nonneg _)
    _ = _ := by ring

end
end ArtinMatthews
