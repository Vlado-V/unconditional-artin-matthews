module

public import ArtinMatthews.MarkedPhysicalHilbertMatrix
public import ArtinMatthews.MarkedPhysicalSourceBad


set_option backward.privateInPublic true
@[expose] public section

/-! The actual GSTSG matrix recovers the literal good physical pairing
for list-constant endpoint vectors. The actual G0 slot symmetry is proved. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section

theorem markedMatrixPairing_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (U : Matrix ι κ ℂ) (f g : κ → ℂ) :
    markedMatrixPairing (Uᴴ*A*U) f g=markedMatrixPairing A (U*ᵥ f) (U*ᵥ g) := by
  simp only [markedMatrixPairing,Matrix.mulVec_mulVec,Matrix.star_mulVec,
    Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul,Matrix.mul_assoc]

theorem markedPhysicalRestrictedMatrix_congruence
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) :
    markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G =
      (markedPhysicalSlotMatrix P (pads+1) Z*markedPhysicalGoodMatrix G)ᴴ *
        markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q *
          (markedPhysicalSlotMatrix P (pads+1) Z*markedPhysicalGoodMatrix G) := by
  simp only [markedPhysicalRestrictedMatrix,Matrix.conjTranspose_mul,
    (markedPhysicalSlotMatrix_isHermitian P (pads+1) Z).eq,
    (markedPhysicalGoodMatrix_isHermitian G).eq,Matrix.mul_assoc]

theorem markedPhysicalSlotMatrix_fixes_good_position
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ))
    (G : MarkedPhysicalState P M Z → Prop)
    (hG : ∀ σ s,G (markedPhysicalSlotEquiv P M Z σ s) ↔ G s)
    (σ₀ : ℝ) (a : Z → ℂ) :
    markedPhysicalSlotMatrix P M Z *ᵥ
        (markedPhysicalGoodMatrix G *ᵥ markedPositionLift
          (fun s : MarkedPhysicalState P M Z => s.1.1) σ₀ a) =
      markedPhysicalGoodMatrix G *ᵥ markedPositionLift
        (fun s : MarkedPhysicalState P M Z => s.1.1) σ₀ a := by
  apply markedPhysicalSlotMatrix_fixes
  intro σ s
  rw [markedPhysicalGoodMatrix_action]
  unfold markedPhysicalGoodVector
  have he := propext (hG σ s)
  rw [he]
  rfl

theorem markedPhysicalRestrictedMatrix_pairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (hV : ∀ j,0<V j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop)
    (hG : ∀ σ s,G (markedPhysicalSlotEquiv P (pads+1) Z σ s) ↔ G s)
    (a b : Z → ℂ) :
    markedMatrixPairing (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G)
      (markedPositionLift (fun s : MarkedPhysicalState P (pads+1) Z => s.1.1)
        (markedPhysicalMass V (pads+1)) a)
      (markedPositionLift (fun s : MarkedPhysicalState P (pads+1) Z => s.1.1)
        (markedPhysicalMass V (pads+1)) b) =
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q
      (markedPhysicalGoodVector G (fun s => a s.1.1))
      (markedPhysicalGoodVector G (fun s => b s.1.1)) := by
  rw [markedPhysicalRestrictedMatrix_congruence,markedMatrixPairing_congruence,
    ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    markedPhysicalSlotMatrix_fixes_good_position P (pads+1) Z G hG,
    markedPhysicalSlotMatrix_fixes_good_position P (pads+1) Z G hG,
    markedPhysicalGoodMatrix_action,markedPhysicalGoodMatrix_action]
  have he (a : Z → ℂ) :
      markedPhysicalGoodVector G (markedPositionLift
        (fun s : MarkedPhysicalState P (pads+1) Z => s.1.1) (markedPhysicalMass V (pads+1)) a) =
      markedPhysicalHilbertVector (markedPhysicalMass V (pads+1))
        (markedPhysicalGoodVector G (fun s => a s.1.1)) := by
    funext s
    by_cases hs : G s <;>
      simp [markedPhysicalGoodVector,markedPositionLift,markedPhysicalHilbertVector,hs]
  rw [he,he]
  exact markedPhysicalEdgeMatrix_pairing P hP V hV pads Z hZ ψ η d₀ Y Q q _ _

theorem markedPhysicalStateToRaw_slots {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (σ : J → Equiv.Perm (Fin M))
    (s : MarkedPhysicalState P M Z) :
    markedPhysicalStateToRaw P hP M Z (markedPhysicalSlotEquiv P M Z σ s) =
      markedRawSlotEquiv σ (markedPhysicalStateToRaw P hP M Z s) := rfl

theorem markedPhysicalActualGood_slots
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (σ : J → Equiv.Perm (Fin (markedPadSlots x)))
    (s : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z) :
    MarkedPhysicalActualGood e x d₀ Y w
      (markedPhysicalSlotEquiv (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z σ s) ↔
      MarkedPhysicalActualGood e x d₀ Y w s := by
  unfold MarkedPhysicalActualGood
  rw [markedPhysicalStateToRaw_slots]
  exact markedRawDirtyGood_slots e x 0 d₀ Y w _ σ

end
end ArtinMatthews
