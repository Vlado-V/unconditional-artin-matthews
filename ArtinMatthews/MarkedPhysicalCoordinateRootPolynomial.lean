module

public import ArtinMatthews.MarkedPhysicalIndexResidueRoot
public import ArtinMatthews.MarkedPhysicalSelectedPolynomialMean
public import ArtinMatthews.MarkedPhysicalCoordinatePolynomialGlobal


set_option backward.privateInPublic true
@[expose] public section

/-! Literal selected-residue root polynomials and their averaged main
terms. The root density and physical mass are explicit and separate. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q : ℝ) {R : ℕ}
  (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
    (markedPadSlots x) (markedMemoryMomentLength x) R) (hR : 1 ≤ R)

def markedPhysicalCoordinateSelectedRoot (q U Vr : ℝ) (T : Finset ℕ) : ℂ :=
  if hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) then
    let S := markedPhysicalBonferroniModulus Finset.univ i.1 T
    let _ : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) Finset.univ i.1 hT).ne'⟩
    ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      markedRootConstantIndicatorSum g U Vr
        (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR)
        ((markedPhysicalCoordinateIndexResidueFactor
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR q T hT g:ℂ)*
          markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
            V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i)
  else 0

def markedPhysicalCoordinateSelectedAverage (q U Vr : ℝ) (T : Finset ℕ) : ℂ :=
  if hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) then
    let S := markedPhysicalBonferroniModulus Finset.univ i.1 T
    let _ : NeZero S := ⟨(markedPhysicalBonferroniModulus_pos
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) Finset.univ i.1 hT).ne'⟩
    ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      (U*Vr/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))) •
        (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR •
          ((markedPhysicalCoordinateIndexResidueFactor
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR q T hT g:ℂ)*
            markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
              (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
              V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i))
  else 0

def markedPhysicalCoordinateRootPolynomial (q U Vr : ℝ) (k : ℕ) : ℂ :=
  if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0) then
    ∑ j ∈ Finset.range (k+1),(-1:ℂ)^j *
      ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard j,
        markedPhysicalCoordinateSelectedRoot e x V ψ η d₀ Y Q i hR q U Vr T
  else 0

def markedPhysicalCoordinateAveragedPolynomial (q U Vr : ℝ) (k : ℕ) : ℂ :=
  if markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0) then
    ∑ j ∈ Finset.range (k+1),(-1:ℂ)^j *
      ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard j,
        markedPhysicalCoordinateSelectedAverage e x V ψ η d₀ Y Q i hR q U Vr T
  else 0

theorem markedPhysicalCoordinateSelectedAverage_eq (q U Vr : ℝ) (T : Finset ℕ)
    (hT : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x)) :
    markedPhysicalCoordinateSelectedAverage e x V ψ η d₀ Y Q i hR q U Vr T =
      (U*Vr/(riemannZeta 2).re) •
        (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR •
          ((markedPhysicalSelectedGuardedMonomialMean
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i.1
            (markedMemoryVisitQ q (markedMemoryMomentLength x))
            (markedPhysicalCoordinateIndexPath i.2.1)
            (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) T hT:ℂ)*
            markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
              (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
              V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i)) := by
  unfold markedPhysicalCoordinateSelectedAverage
  rw [dite_eq_left hT]
  dsimp only
  unfold markedPhysicalSelectedGuardedMonomialMean
  dsimp only
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sum,
    div_eq_mul_inv,mul_inv_rev,Finset.sum_mul,Finset.mul_sum,
    markedPhysicalCoordinateIndexResidueFactor]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem markedPhysicalCoordinateAveragedPolynomial_eq (q U Vr : ℝ) (k : ℕ) :
    markedPhysicalCoordinateAveragedPolynomial e x V ψ η d₀ Y Q i hR q U Vr k =
      (U*Vr/(riemannZeta 2).re) •
        markedPhysicalCoordinatePolynomialTerm e x V ψ η d₀ Y Q i hR q U Vr k := by
  let c := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  let v := markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR
  have hs : (∑ j ∈ Finset.range (k+1),(-1:ℂ)^j *
      ∑ T ∈ (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
        markedPhysicalPathUsedPrimes Finset.univ i.1).powersetCard j,
        markedPhysicalCoordinateSelectedAverage e x V ψ η d₀ Y Q i hR q U Vr T) =
      (U*Vr/(riemannZeta 2).re) • (v •
        ((markedPhysicalSelectedGuardedPolynomialMean
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i.1 q
          (markedPhysicalCoordinateIndexPath i.2.1)
          (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) k:ℂ)*c)) := by
    unfold markedPhysicalSelectedGuardedPolynomialMean
    simp only [Complex.real_smul,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_one,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro T hT
    have ht : T ⊆ markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) :=
      fun p hp => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1
    rw [dite_eq_left ht,markedPhysicalCoordinateSelectedAverage_eq e x V ψ η d₀ Y Q i hR q U Vr T ht]
    change (-1:ℂ)^j * _ = _
    simp only [Complex.real_smul]
    dsimp only [c,v]
    ring
  unfold markedPhysicalCoordinateAveragedPolynomial markedPhysicalCoordinatePolynomialTerm
    markedPhysicalCoordinatePathApply
  rw [hs,markedPhysicalSelectedGuardedPolynomialMean_eq]
  by_cases ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v)
  · by_cases hc : markedPhysicalCoordinateIndexCoefficient
        (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i=0
    · simp [ha,hc,c]
    · by_cases hl : markedPhysicalCoordinateIndexPath i.2.1 (Fin.last (markedMemoryMomentLength x))=(1,0)
      · simp [ha,hc,hl,c,v,Complex.real_smul]
      · simp [ha,hc,hl]
  · simp [ha]

end
end ArtinMatthews
