module

public import ArtinMatthews.MarkedPhysicalCoordinateCopyBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The original V normalizers give a fixed uniform edge constant.
Only the proved Q^3 cost is repeated along the actual full path. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedPhysicalCoordinateUniformBound (K : ℕ) (v₀ H W : ℝ) : ℝ :=
  5*(v₀⁻¹)^K*H^2*W

theorem markedPhysicalCoordinateUniformBound_nonneg (K : ℕ) {v₀ H W : ℝ}
    (hv0 : 0 < v₀) (hW : 0 ≤ W) : 0 ≤ markedPhysicalCoordinateUniformBound K v₀ H W := by
  unfold markedPhysicalCoordinateUniformBound
  positivity

theorem markedPhysicalCoordinateEdgeBound_le {J : Type*} [Fintype J]
    (V : J → ℝ) {v₀ H W : ℝ} (hv0 : 0 < v₀) (hV : ∀ j,v₀ ≤ V j) (hW : 0 ≤ W) :
    markedPhysicalCoordinateEdgeBound V H W ≤ markedPhysicalCoordinateUniformBound (Fintype.card J) v₀ H W := by
  unfold markedPhysicalCoordinateEdgeBound markedPhysicalCoordinateUniformBound
  gcongr
  exact markedPhysicalCoordinateKernel_atom_bound V hv0 hV

theorem markedPhysicalCoordinatePathKernel_uniform_norm
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q H W v₀ : ℝ) (hv0 : 0 < v₀) (hV : ∀ j,v₀ ≤ V j)
    (hY : 1 ≤ Y) (hQ : 1 ≤ Q) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hη : ∀ t,‖η t‖ ≤ H) (hψ : ∀ t,‖ψ t‖ ≤ W)
    (n : ℕ) (path : Fin (n+1) → MarkedPhysicalState P (pads+1) Z)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z : Fin (n+1) → ℤ × ℤ) :
    ‖markedPhysicalCoordinatePathKernel P hP V pads Z ψ η d₀ Y Q n path copies z‖ ≤
      (markedPhysicalCoordinateUniformBound (Fintype.card J) v₀ H W*Q^3)^n := by
  apply (markedPhysicalCoordinatePathKernel_norm_le P hP V pads Z ψ η d₀ Y Q H W
    hY hQ hH hW hη hψ n path copies z).trans
  exact pow_le_pow_left₀ (by unfold markedPhysicalCoordinateEdgeBound; positivity)
    (mul_le_mul_of_nonneg_right (markedPhysicalCoordinateEdgeBound_le V hv0 hV hW) (by positivity)) n

end ArtinMatthews
