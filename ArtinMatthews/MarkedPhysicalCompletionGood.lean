module

public import ArtinMatthews.MarkedPhysicalRootCoordinates
public import ArtinMatthews.MarkedRawGoodRootBridge


set_option backward.privateInPublic true
@[expose] public section

/-! The physical good test is independent of the determinant-one
completion at the source root. Thus its original complement can be
replaced by the canonical completion used for integer-root counting. -/

noncomputable section
namespace ArtinMatthews

theorem markedPhysical_completion_first_shift (root completion other : ℤ × ℤ)
    (hc : markedMinorIntegerDet root completion = 1)
    (ho : markedMinorIntegerDet root other = 1) :
    other.1 = completion.1 + markedMinorIntegerDet other completion * root.1 := by
  have h := congrArg Prod.fst (markedPhysicalRootLift_coordinates root completion other hc)
  change markedMinorIntegerDet other completion * root.1 +
    markedMinorIntegerDet root other * completion.1 = other.1 at h
  rw [ho, one_mul] at h
  linarith

theorem markedPhysical_completion_ratio_circle (root completion other : ℤ × ℤ)
    (hc : markedMinorIntegerDet root completion = 1)
    (ho : markedMinorIntegerDet root other = 1) :
    (((other.1 : ℝ)/(root.1 : ℝ)) : AddCircle (1 : ℝ)) =
      (((completion.1 : ℝ)/(root.1 : ℝ)) : AddCircle (1 : ℝ)) := by
  by_cases hr : root.1 = 0
  · simp only [hr, Int.cast_zero, div_zero]
  have hrR : (root.1 : ℝ) ≠ 0 := by exact_mod_cast hr
  have hs : (other.1 : ℝ) = (completion.1 : ℝ) +
      (markedMinorIntegerDet other completion : ℝ) * (root.1 : ℝ) := by
    exact_mod_cast markedPhysical_completion_first_shift root completion other hc ho
  have hratio : (other.1 : ℝ)/(root.1 : ℝ) =
      (completion.1 : ℝ)/(root.1 : ℝ) + (markedMinorIntegerDet other completion : ℝ) := by
    apply (div_eq_iff hrR).mpr
    calc
      _ = (completion.1 : ℝ) + (markedMinorIntegerDet other completion : ℝ) * (root.1 : ℝ) := hs
      _ = _ := by field_simp
  rw [hratio, AddCircle.coe_add]
  have hz : (((markedMinorIntegerDet other completion : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨markedMinorIntegerDet other completion, by simp⟩
  rw [hz, add_zero]

theorem markedRawDirtyGood_zero_canonical_completion
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z)
    (completion : ℤ × ℤ)
    (hw : markedMinorIntegerDet s.1.1 (w s.1) = 1)
    (hc : markedMinorIntegerDet s.1.1 completion = 1) :
    MarkedRawDirtyGood e x 0 d₀ Y w s ↔
      (((completion.1 : ℝ)/(s.1.1.1 : ℝ)) : AddCircle (1 : ℝ)) ∉
        markedRawBadRootSet e x d₀ Y s.2.1 := by
  rw [markedRawDirtyGood_iff_not_badRootSet]
  simp only [markedMinorIntegerTau, zero_mul, add_zero]
  rw [markedPhysical_completion_ratio_circle s.1.1 completion (w s.1) hc hw]

end ArtinMatthews
