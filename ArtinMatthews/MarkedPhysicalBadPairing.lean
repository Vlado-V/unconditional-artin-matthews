module

public import ArtinMatthews.MarkedPhysicalBadBlock
public import ArtinMatthews.MarkedPhysicalUnionRootSum
public import ArtinMatthews.MarkedPhysicalAbsoluteReindex


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite summation of the physical source-bad absolute pairing. -/
noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedPhysical_source_bad_absolute_le_majorant_of_cover
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ)
    (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (hw : ∀ z, markedMinorIntegerDet z.1 (w z) = 1)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H F G R : ℝ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hG : 0 ≤ G) (hη : ∀ t, ‖η t‖ ≤ H)
    (hY : 0 < Y) (hsupp : ∀ v, ψ v ≠ 0 → |v| ≤ R)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ F) (hg : ∀ s, ‖g s‖ ≤ G)
    {A B C D U : ℝ} (hA : 1 < A) (hC : 1 < C) (hU : 0 < U) (hUA : U ≤ A) (hBU : B ≤ 16*U)
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D)
    (hcover : ∀ u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1),
      ∀ θ : AddCircle (1 : ℝ),
        (if θ ∈ markedRawBadRootSet e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) then (1 : ℝ) else 0) ≤
          markedRawBadRootArcMajorant e x d₀ Y (markedPhysicalActualEdgeRawSource e x u) θ) :
    markedPhysicalEdgeAbsolutePairing (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
      (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
      ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1
      (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f) g ≤
      (H^2*F*G) * markedPhysicalActualUnionMajorantSum e x hdis d₀ Y A B C D R Q ψ := by
  let P := fun j => markedLogPowerBand (e j) x
  let hP := fun j p (hp : p ∈ P j) => (mem_markedLogPowerBand.mp hp).1
  let V := fun j => bandReciprocalMass (P j)
  have hV : ∀ j, 0 ≤ V j := by
    intro j
    dsimp only [V, bandReciprocalMass]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  rw [markedPhysicalEdgeAbsolutePairing_eq_canonical_sum P hP hdis V
    ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1
    (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f) g hA hC hbox]
  unfold markedPhysicalCanonicalAbsolutePairingSum markedPhysicalActualUnionMajorantSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : MarkedPhysicalMarkingDistinct u
  · simp only [dite_eq_left hu]
    let : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
    have hb := markedPhysical_canonical_source_bad_block_le e x d₀ Y Q V hV Z hZ w hw
      ψ η H F G R hH hF hG hη hY hsupp f g hf hg u
      (markedPhysicalMarkingProduct_squarefree hP hdis u hu) hA hC hU hUA hBU hbox (hcover u)
    dsimp only [markedPhysicalSourceBadBlock, markedPhysicalSourceBadTerm] at hb
    apply hb.trans_eq
    ring
  · simp only [dite_eq_right hu, mul_zero, le_refl]

theorem markedPhysical_source_bad_absolute_le_majorant
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (d₀ Y Q : ℝ)
      (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
      (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
      (w : Z → ℤ × ℤ), (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      ∀ (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H F G R : ℝ),
      0 ≤ H → 0 ≤ F → 0 ≤ G → (∀ t, ‖η t‖ ≤ H) →
      0 < Y → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
      ∀ (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ),
      (∀ s, ‖f s‖ ≤ F) → (∀ s, ‖g s‖ ≤ G) →
      ∀ A B C D U : ℝ, 1 < A → 1 < C → 0 < U → U ≤ A → B ≤ 16*U →
      Z ⊆ markedPhysicalPrimitiveBox A B C D →
      markedPhysicalEdgeAbsolutePairing (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1
        (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f) g ≤
        (H^2*F*G) * markedPhysicalActualUnionMajorantSum e x hdis d₀ Y A B C D R Q ψ := by
  filter_upwards [markedRawBadRoot_indicator_le_arcs_eventually e he] with x hx
  intro d₀ Y Q hdis Z hZ w hw ψ η H F G R hH hF hG hη hY hsupp f g hf hg A B C D U hA hC hU hUA hBU hbox
  exact markedPhysical_source_bad_absolute_le_majorant_of_cover e x d₀ Y Q hdis Z hZ w hw
    ψ η H F G R hH hF hG hη hY hsupp f g hf hg hA hC hU hUA hBU hbox
    (fun u θ => hx d₀ Y (markedPhysicalActualEdgeRawSource e x u) θ)

end ArtinMatthews
