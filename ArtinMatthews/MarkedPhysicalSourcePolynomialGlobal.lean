module

public import ArtinMatthews.MarkedPhysicalIndexPolynomialRootSum
public import ArtinMatthews.MarkedPhysicalRootPolynomialError


set_option backward.privateInPublic true
@[expose] public section

/-! Original full-box damping, its actual guarded polynomial, and the
positive odd-tail majorant on one common physical coordinate carrier. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q q U Vr : ℝ) {R : ℕ}
  (S : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
    (markedPadSlots x) (markedMemoryMomentLength x) → ℕ) (hS : ∀ a,S a≠0)

def markedPhysicalSourceDampingGlobal
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i *
        (letI : NeZero (S i.1) := ⟨hS i.1⟩
         ∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) Vr (2*Vr),
           markedPhysicalCoordinateIndexDamping (fun j => markedLogPowerBand (e j) x)
             ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) q
             (MarkedPhysicalActualGood e x d₀ Y w) i r)

def markedPhysicalSourcePolynomialGlobal (hR : 1 ≤ R) (k : ℕ) : ℂ :=
  (markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x):ℂ)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i *
        (letI : NeZero (S i.1) := ⟨hS i.1⟩
         ∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) Vr (2*Vr),
           markedPhysicalIndexPolynomialWeight e x d₀ Y U Vr i hR q k r)

def markedPhysicalSourceTailGlobal (hR : 1 ≤ R) (k : ℕ) : ℝ :=
  markedPhysicalMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x)*
    ∑ i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R,
      ‖markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i‖ *
        (letI : NeZero (S i.1) := ⟨hS i.1⟩
         ∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) Vr (2*Vr),
           markedPhysicalIndexTailWeight e x d₀ Y U Vr i hR q k r)

theorem markedPhysicalSourcePolynomialGlobal_eq_root (hR : 1 ≤ R)
    (hU : 1 < U) (hVr : 1 < Vr) (k : ℕ) :
    markedPhysicalSourcePolynomialGlobal e x ψ η d₀ Y Q q U Vr S hS hR k=
      markedPhysicalCoordinateRootGlobal e x ψ η d₀ Y Q hR q U Vr k := by
  unfold markedPhysicalSourcePolynomialGlobal markedPhysicalCoordinateRootGlobal
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let : NeZero (S i.1) := ⟨hS i.1⟩
  exact markedPhysicalIndexPolynomial_fixed_root_sum e x _ ψ η d₀ Y Q i hR q U Vr hU hVr (S i.1) k

theorem markedPhysicalSourceDampingGlobal_error (hR : 1 ≤ R)
    (hdis : Pairwise (fun j k => Disjoint (markedLogPowerBand (e j) x) (markedLogPowerBand (e k) x)))
    (hn : 0 < markedMemoryMomentLength x) (hU : 1 < U) (hVr : 1 < Vr)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ)
    (hw : ∀ a,markedMinorIntegerDet a.1 (w a)=1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    ‖markedPhysicalSourceDampingGlobal e x ψ η d₀ Y Q q U Vr S hS (R := R) w-
      markedPhysicalSourcePolynomialGlobal e x ψ η d₀ Y Q q U Vr S hS hR (2*m)‖ ≤
      markedPhysicalSourceTailGlobal e x ψ η d₀ Y Q q U Vr S hS hR (2*m+1) := by
  have hm : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) :=
    markedPhysicalMass_nonneg _ _ (fun _ => by unfold bandReciprocalMass; positivity)
  unfold markedPhysicalSourceDampingGlobal markedPhysicalSourcePolynomialGlobal markedPhysicalSourceTailGlobal
  rw [← mul_sub,← Finset.sum_sub_distrib,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hm).trans
  apply mul_le_mul_of_nonneg_left _ hm
  apply Finset.sum_le_sum
  intro i _
  let : NeZero (S i.1) := ⟨hS i.1⟩
  let C := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  change ‖C * _ - C * _‖ ≤ ‖C‖ * _
  rw [← mul_sub,← Finset.sum_sub_distrib,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun r _ =>
    markedPhysicalIndexDamping_bonferroni_error e x d₀ Y U Vr hdis hn i hR hU hVr r w hw hq0 hq1 m)

end
end ArtinMatthews
