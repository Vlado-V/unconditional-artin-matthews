module

public import ArtinMatthews.MarkedPhysicalCoordinateRootPolynomial
public import ArtinMatthews.MarkedPhysicalGlobalResidueBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Finite summation of the actual selected-modulus root errors. The
class count includes every selected subset and every residue class. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q : ℝ) {R : ℕ}
  (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
    (markedPadSlots x) (markedMemoryMomentLength x) R) (hR : 1 ≤ R)

theorem markedPhysicalCoordinateSelectedRoot_error (q U Vr ε : ℝ) (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x))
    (he : ∀ g : Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T)),
      let r := markedPhysicalCoordinateIndexResidueFactor
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR q T hT g
      let c := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
      ‖markedRootConstantIndicatorSum g U Vr (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR)
          ((r:ℂ)*c)-
        (U*Vr/((riemannZeta 2).re*
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
            (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ))) •
          (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR • ((r:ℂ)*c))‖ ≤ ε) :
    ‖markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T-
      markedPhysicalCoordinateSelectedAverage e x V ψ η d₀ Y Q i hR q U Vr T‖ ≤
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
        (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ)*ε := by
  let S := markedPhysicalBonferroniModulus Finset.univ i.1 T
  let : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) Finset.univ i.1 hT).ne'⟩
  unfold markedPhysicalCoordinateSelectedRoot markedPhysicalCoordinateSelectedAverage
  rw [dite_eq_left hT,dite_eq_left hT]
  dsimp only
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),ε :=
      Finset.sum_le_sum (fun g _ => he g)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,S]

omit [DecidableEq J] in
theorem markedPhysicalSelectedResidueCount_mono
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) {k l : ℕ} (hkl : k ≤ l) :
    markedPhysicalSelectedResidueCount e x a k ≤ markedPhysicalSelectedResidueCount e x a l := by
  unfold markedPhysicalSelectedResidueCount
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hkl 1))
    (fun _ _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem markedPhysicalCoordinateRootPolynomial_error (q U Vr ε : ℝ) (hε : 0 ≤ ε)
    (k : ℕ)
    (he : ∀ (T : Finset ℕ),
      T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ i.1 → T.card ≤ k →
      ‖markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T-
        markedPhysicalCoordinateSelectedAverage e x V ψ η d₀ Y Q i hR q U Vr T‖ ≤
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
          (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ)*ε) :
    ‖markedPhysicalCoordinateRootPolynomial e x V ψ η d₀ Y Q i hR q U Vr k-
      markedPhysicalCoordinateAveragedPolynomial e x V ψ η d₀ Y Q i hR q U Vr k‖ ≤
      markedPhysicalSelectedResidueCount e x i.1 k*ε := by
  unfold markedPhysicalCoordinateRootPolynomial markedPhysicalCoordinateAveragedPolynomial
  split_ifs
  · rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range (k+1),∑ T ∈
          (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
            markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard j,
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
            (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ)*ε := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← mul_sub,← Finset.sum_sub_distrib,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro T hT
        have ht := Finset.mem_powersetCard.mp hT
        exact he T ht.1 (ht.2.le.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      _ = _ := by simp only [markedPhysicalSelectedResidueCount,Finset.sum_mul]
  · simp only [sub_self,norm_zero]
    apply mul_nonneg _ hε
    unfold markedPhysicalSelectedResidueCount
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

def markedPhysicalCoordinateRootGlobal (q U Vr : ℝ) (k : ℕ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      markedPhysicalCoordinateRootPolynomial e x
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hR q U Vr k

def markedPhysicalCoordinateAveragedGlobal (q U Vr : ℝ) (k : ℕ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      markedPhysicalCoordinateAveragedPolynomial e x
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hR q U Vr k

theorem markedPhysicalCoordinateAveragedGlobal_eq (q U Vr : ℝ) :
    markedPhysicalCoordinateAveragedGlobal e x ψ η d₀ Y Q hR q U Vr
      (2*markedPhysicalBonferroniDepth x) =
      (U*Vr/(riemannZeta 2).re) •
        markedPhysicalCoordinatePolynomialGlobal e x ψ η d₀ Y Q q U Vr R hR := by
  unfold markedPhysicalCoordinateAveragedGlobal markedPhysicalCoordinatePolynomialGlobal
  simp_rw [markedPhysicalCoordinateAveragedPolynomial_eq]
  simp only [Algebra.smul_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem markedPhysicalCoordinateRootGlobal_error (q U Vr ε : ℝ) (hε : 0 ≤ ε) (k : ℕ)
    (he : ∀ (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R) (T : Finset ℕ),
      T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ i.1 → T.card ≤ k →
      ‖markedPhysicalCoordinateSelectedRoot e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ψ η d₀ Y Q i hR q U Vr T-
        markedPhysicalCoordinateSelectedAverage e x
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
          ψ η d₀ Y Q i hR q U Vr T‖ ≤
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2)
          (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))):ℝ)*ε) :
    ‖markedPhysicalCoordinateRootGlobal e x ψ η d₀ Y Q hR q U Vr k-
      markedPhysicalCoordinateAveragedGlobal e x ψ η d₀ Y Q hR q U Vr k‖ ≤
      (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
        ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x) R,
          markedPhysicalSelectedResidueCount e x i.1 k)*ε := by
  have hm : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) :=
    markedPhysicalMass_nonneg _ _ (fun _ => by unfold bandReciprocalMass; positivity)
  unfold markedPhysicalCoordinateRootGlobal markedPhysicalCoordinateAveragedGlobal
  rw [← mul_sub,← Finset.sum_sub_distrib,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hm]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hm).trans
  calc
    _ ≤ markedPhysicalMass
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
        ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
          (markedPadSlots x) (markedMemoryMomentLength x) R,
          markedPhysicalSelectedResidueCount e x i.1 k*ε := by
      apply mul_le_mul_of_nonneg_left _ hm
      exact Finset.sum_le_sum (fun i _ => markedPhysicalCoordinateRootPolynomial_error
        e x _ ψ η d₀ Y Q i hR q U Vr ε hε k (he i))
    _ = _ := by rw [← Finset.sum_mul,mul_assoc]

end
end ArtinMatthews
