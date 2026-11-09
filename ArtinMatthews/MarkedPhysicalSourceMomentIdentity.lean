module

public import ArtinMatthews.MarkedPhysicalSourcePolynomialGlobal
public import ArtinMatthews.MarkedPhysicalMomentRootDamping


set_option backward.privateInPublic true
@[expose] public section

/-! The source damping functional is the literal original physical
even moment on the full primitive box, with its original mass. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPhysicalPositionMoment_eq_sourceDamping
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (hx : 1 < x)
    (hdis : Pairwise (fun j k => Disjoint (markedLogPowerBand (e j) x) (markedLogPowerBand (e k) x)))
    (hV : ∀ j,0 < bandReciprocalMass (markedLogPowerBand (e j) x))
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K U Vr : ℝ)
    (hd₀ : 0 < d₀) (hY : 0 < Y) (hK : 0 ≤ K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (hU : 1 < U) (hVr : 1 < Vr)
    (S : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x) → ℕ) (hS : ∀ a,S a≠0)
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr)) → ℤ × ℤ) :
    markedPhysicalPositionMoment (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
      (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
      (markedPhysicalRestrictedMatrix (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
        (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q
        (MarkedPhysicalActualGood e x d₀ Y w))
      ⌈(Real.log x)^(1/2:ℝ)/2⌉₊ =
    (markedPhysicalSourceDampingGlobal e x ψ η d₀ Y Q q U Vr S hS
      (R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)) w).re := by
  have hn := markedPhysicalMomentLength_pos hx
  have hr : 0 < ⌈(Real.log x)^(1/2:ℝ)/2⌉₊ := by
    unfold markedMemoryMomentLength at hn
    omega
  have hm := markedPhysicalPositionMoment_root_damping
    (fun j => markedLogPowerBand (e j) x) (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
    ⌊(Real.log x)^(1/100:ℝ)⌋₊ (markedPhysicalPrimitiveBox U (16*U) Vr (2*Vr))
    (fun _ hz => (Finset.mem_filter.mp hz).2) ψ η d₀ Y Q q hdis
    (MarkedPhysicalActualGood e x d₀ Y w) hV ⌈(Real.log x)^(1/2:ℝ)/2⌉₊ hr
    K U Vr hd₀ hY hK hψ hU hVr (Finset.Subset.refl _) S hS
  refine hm.trans ?_
  unfold markedPhysicalSourceDampingGlobal markedPhysicalMomentRootDampingSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

end
end ArtinMatthews
