module

public import ArtinMatthews.MarkedPhysicalSourcePolynomialGlobal
public import ArtinMatthews.MarkedPhysicalIndexTailRootSum
public import ArtinMatthews.MarkedPhysicalRootTailNormMass


set_option backward.privateInPublic true
@[expose] public section

/-! The original positive physical tail is controlled before any
complex cancellation, using the exact selected-modulus reindexing. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q q U Vr : ℝ) {R : ℕ}
  (S : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
    (markedPadSlots x) (markedMemoryMomentLength x) → ℕ) (hS : ∀ a,S a≠0)

theorem markedPhysicalSourceTailGlobal_le_root_norm (hR : 1 ≤ R)
    (hU : 1 < U) (hVr : 1 < Vr) (k : ℕ) :
    markedPhysicalSourceTailGlobal e x ψ η d₀ Y Q q U Vr S hS hR k ≤
      markedPhysicalSelectedRootTailNormMass e x ψ η d₀ Y Q q U Vr hR k := by
  have hm : 0 ≤ markedPhysicalMass
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) (markedPadSlots x) :=
    markedPhysicalMass_nonneg _ _ (fun _ => by unfold bandReciprocalMass; positivity)
  unfold markedPhysicalSourceTailGlobal markedPhysicalSelectedRootTailNormMass
  apply mul_le_mul_of_nonneg_left _ hm
  apply Finset.sum_le_sum
  intro i _
  let : NeZero (S i.1) := ⟨hS i.1⟩
  let C := markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
  change ‖C‖ * (∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) Vr (2*Vr),
      markedPhysicalIndexTailWeight e x d₀ Y U Vr i hR q k r) ≤ _
  calc
    _ ≤ ‖C‖ * |∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) Vr (2*Vr),
        markedPhysicalIndexTailWeight e x d₀ Y U Vr i hR q k r| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
    _ = ‖C * ∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) Vr (2*Vr),
        (markedPhysicalIndexTailWeight e x d₀ Y U Vr i hR q k r:ℂ)‖ := by
      rw [norm_mul,← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := by
      have ht := markedPhysicalIndexTail_fixed_root_sum e x
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) ψ η d₀ Y Q i hR q U Vr hU hVr (S i.1) k
      change C * _ = _ at ht
      rw [ht]
      split_ifs
      · exact norm_sum_le _ _
      · simp only [norm_zero]
        exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem markedPhysicalSourceDampingGlobal_root_error (hR : 1 ≤ R)
    (hdis : Pairwise (fun j k => Disjoint (markedLogPowerBand (e j) x) (markedLogPowerBand (e k) x)))
    (hn : 0 < markedMemoryMomentLength x) (hU : 1 < U) (hVr : 1 < Vr)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ)
    (hw : ∀ a,markedMinorIntegerDet a.1 (w a)=1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖markedPhysicalSourceDampingGlobal e x ψ η d₀ Y Q q U Vr S hS (R := R) w-
      markedPhysicalCoordinateRootGlobal e x ψ η d₀ Y Q hR q U Vr
        (2*markedPhysicalBonferroniDepth x)‖ ≤
      markedPhysicalOddRootDiscrepancyMass e x ψ η d₀ Y Q hR q U Vr+
      (U*Vr/(riemannZeta 2).re)*
        markedPhysicalCoordinateBonferroniTailMass e x ψ η d₀ Y Q q U Vr R hR := by
  have h := markedPhysicalSourceDampingGlobal_error e x ψ η d₀ Y Q q U Vr S hS hR
    hdis hn hU hVr w hw hq0 hq1 (markedPhysicalBonferroniDepth x)
  rw [markedPhysicalSourcePolynomialGlobal_eq_root e x ψ η d₀ Y Q q U Vr S hS hR hU hVr] at h
  exact h.trans ((markedPhysicalSourceTailGlobal_le_root_norm e x ψ η d₀ Y Q q U Vr S hS hR hU hVr _).trans
    (markedPhysicalSelectedRootOddTailNormMass_le e x ψ η d₀ Y Q q U Vr hR hq0 hq1
      (mul_nonneg (by linarith) (by linarith))))

end
end ArtinMatthews
