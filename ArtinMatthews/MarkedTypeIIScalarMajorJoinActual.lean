module

public import ArtinMatthews.MarkedTypeIIScalarMajorJoin
public import ArtinMatthews.MarkedTypeIISharedMajorActual


set_option backward.privateInPublic true
@[expose] public section

/-! The original scalar delta minus the unrestricted fixed-character
major differs from the literal coprime minor detector by the proved
shared-label correction on the actual Type II rectangle. -/
namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped ComplexConjugate

theorem markedPhysicalScalar_fixed_delta_sub_major_error_log_saving
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j)
    {Mχ : ℕ} (ξ : DirichletCharacter ℂ Mχ)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (R W δ C Qexp K D : ℝ)
    (hR : 0 ≤ R) (hW : 0 ≤ W) (hδ : 0 < δ) (hK : 0 < K)
    (hη : ∀ u,‖η u‖ ≤ 1) (hηsupp : Function.support η ⊆ Set.Icc 1 4)
    (hψ : ∀ u,‖ψ u‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ L : ℝ in atTop, ∀ H U Y modulation : ℝ, ∀ (S : Finset ℕ) (l r : ℕ) (β : ℕ → ℂ),
      Real.exp (δ*L) ≤ H → Real.exp (δ*L) ≤ U → H*U ≤ K*Real.exp L →
      (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
      U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U → 0 < Y →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^C) →
      let P := fun j => markedLogPowerBand (e j) (Real.exp L)
      let Wrough := Real.exp (L^(6/25:ℝ))
      let αχ := fun m => ξ (m:ℕ)*markedMajorCenteredCoefficient Wrough modulation m
      let βχ := fun n => ξ (n:ℕ)*β n
      ‖(markedPhysicalCoprimeScalarDetectorSum P S (Icc l r) η Y (markedRawEdgeDeltaDetector ψ Y) αχ βχ -
        markedMajorFixedIntervalPairSum P ξ η ψ (L^Qexp) Y Wrough modulation S S l r β) -
        markedPhysicalCoprimeScalarDetectorSum P S (Icc l r) η Y (markedBanEdgeKernel ψ (L^Qexp) Y) αχ βχ‖ ≤
          (Y*(H*U))*L^(-D) := by
  filter_upwards [markedMajorFixedIntervalPairSum_coprime_error_log_saving e he ξ η ψ
    R W δ C Qexp K D hR hW hδ hK hη hηsupp hψ hsupp] with L h
  intro H U Y modulation S l r β hH hU hX hS hl hr hY hβ
  dsimp only
  let P := fun j => markedLogPowerBand (e j) (Real.exp L)
  let Wrough := Real.exp (L^(6/25:ℝ))
  have hd := markedPhysicalScalar_fixed_delta_sub_major_eq P ξ S l r η ψ
    (L^Qexp) Y Wrough modulation β hY hηsupp
  dsimp only at hd
  rw [hd,sub_sub_cancel_left,norm_neg]
  rw [← markedMajorFixedIntervalPairSum_sub_coprime P η ψ (L^Qexp) Y Wrough modulation
    S S l r β ξ hY hηsupp]
  exact h H U Y modulation S S l r β hH hU hX hS hS hl hr hY hβ

end
end ArtinMatthews
