module

public import ArtinMatthews.MarkedPhysicalRootPolynomialError


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute selected-root errors, before any cancellation in the
Bonferroni polynomial. The physical mass and every selected modulus are
literal. A single level is charged to the proved full class count. -/

namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def markedPhysicalCoordinateDiscrepancyMass (e : J → ℝ) (x : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ) {R : ℕ} (hR : 1≤R)
    (q U Vr : ℝ) (k : ℕ) : ℝ :=
  markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
          markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
        ‖markedPhysicalCoordinateSelectedRoot e x
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            ψ η d₀ Y Q i hR q U Vr T-
          markedPhysicalCoordinateSelectedAverage e x
            (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
            ψ η d₀ Y Q i hR q U Vr T‖

def markedPhysicalOddRootDiscrepancyMass (e : J → ℝ) (x : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ) {R : ℕ} (hR : 1≤R)
    (q U Vr : ℝ) : ℝ :=
  markedPhysicalCoordinateDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr
    (2*markedPhysicalBonferroniDepth x+1)

omit [DecidableEq J] in
theorem markedPhysicalSelectedResidueLevel_le (e : J → ℝ) (x : ℝ)
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) (k l : ℕ) (hkl : k≤l) :
    (∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ a).powersetCard k,
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ a T))):ℝ)) ≤
      markedPhysicalSelectedResidueCount e x a l := by
  unfold markedPhysicalSelectedResidueCount
  apply Finset.single_le_sum (f := fun j =>
    ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
      markedPhysicalPathUsedPrimes Finset.univ a).powersetCard j,
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ a T))):ℝ))
  · exact fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hkl)

theorem markedPhysicalCoordinateDiscrepancyMass_le (e : J → ℝ) (x : ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ) {R : ℕ} (hR : 1≤R)
    (q U Vr ε : ℝ) (hε : 0≤ε) (k l : ℕ) (hkl : k≤l)
    (he : ∀ (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R) (T : Finset ℕ),
      T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ i.1 → T.card≤k →
      ‖markedPhysicalCoordinateSelectedRoot e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hR q U Vr T-
        markedPhysicalCoordinateSelectedAverage e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hR q U Vr T‖ ≤
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
          (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ)*ε) :
    markedPhysicalCoordinateDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr k ≤
      (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
        ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x) R,
          markedPhysicalSelectedResidueCount e x i.1 l)*ε := by
  have hm : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) :=
    markedPhysicalMass_nonneg _ _ (fun _ => by unfold bandReciprocalMass; positivity)
  unfold markedPhysicalCoordinateDiscrepancyMass
  calc
    _ ≤ markedPhysicalMass
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
        ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x) R,
          markedPhysicalSelectedResidueCount e x i.1 l*ε := by
      apply mul_le_mul_of_nonneg_left _ hm
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
              markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
              (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ)*ε := by
          apply Finset.sum_le_sum
          intro T hT
          have ht := Finset.mem_powersetCard.mp hT
          exact he i T ht.1 ht.2.le
        _ = (∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
              markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard k,
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
              (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ))*ε :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (markedPhysicalSelectedResidueLevel_le e x i.1 k l hkl) hε
    _ = _ := by rw [← Finset.sum_mul,mul_assoc]

end
end ArtinMatthews
