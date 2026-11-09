module

public import ArtinMatthews.MarkedPhysicalGoodPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Exact integral target coordinates at a primitive source root. A
determinant-one completion gives an actual bijection on integer targets;
the enlarged target box becomes a one-dimensional root interval test. -/
namespace ArtinMatthews
noncomputable section

def markedPhysicalRootCoordinates (root completion target : ℤ × ℤ) : ℤ × ℤ :=
  (markedMinorIntegerDet target completion,markedMinorIntegerDet root target)

def markedPhysicalRootLift (root completion z : ℤ × ℤ) : ℤ × ℤ :=
  (z.1*root.1+z.2*completion.1,z.1*root.2+z.2*completion.2)

theorem markedPhysicalRootLift_coordinates (root completion target : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) :
    markedPhysicalRootLift root completion (markedPhysicalRootCoordinates root completion target) = target := by
  apply Prod.ext
  · change markedMinorIntegerDet target completion*root.1 + markedMinorIntegerDet root target*completion.1 = target.1
    calc
      _ = markedMinorIntegerDet root completion*target.1 := by unfold markedMinorIntegerDet; ring
      _ = _ := by rw [hdet,one_mul]
  · change markedMinorIntegerDet target completion*root.2 + markedMinorIntegerDet root target*completion.2 = target.2
    calc
      _ = markedMinorIntegerDet root completion*target.2 := by unfold markedMinorIntegerDet; ring
      _ = _ := by rw [hdet,one_mul]

theorem markedPhysicalRootCoordinates_lift (root completion z : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) :
    markedPhysicalRootCoordinates root completion (markedPhysicalRootLift root completion z) = z := by
  apply Prod.ext
  · change markedMinorIntegerDet (markedPhysicalRootLift root completion z) completion = z.1
    calc
      _ = z.1*markedMinorIntegerDet root completion := by
        unfold markedPhysicalRootLift markedMinorIntegerDet
        ring
      _ = _ := by rw [hdet,mul_one]
  · change markedMinorIntegerDet root (markedPhysicalRootLift root completion z) = z.2
    calc
      _ = z.2*markedMinorIntegerDet root completion := by
        unfold markedPhysicalRootLift markedMinorIntegerDet
        ring
      _ = _ := by rw [hdet,mul_one]

def markedPhysicalRootEquiv (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun := markedPhysicalRootCoordinates root completion
  invFun := markedPhysicalRootLift root completion
  left_inv target := markedPhysicalRootLift_coordinates root completion target hdet
  right_inv z := markedPhysicalRootCoordinates_lift root completion z hdet

theorem markedPhysicalRootCoordinates_source (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) :
    markedPhysicalRootCoordinates root completion root = (1,0) := by
  apply Prod.ext
  · exact hdet
  · change markedMinorIntegerDet root root = 0
    unfold markedMinorIntegerDet
    ring

theorem markedPhysicalRootCoordinates_tau (root completion target : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) (hroot : root.1 ≠ 0) :
    markedMinorIntegerTau ((completion.1:ℝ)/root.1)
      (markedPhysicalRootCoordinates root completion target) = (target.1:ℝ)/root.1 := by
  have he := congrArg Prod.fst (markedPhysicalRootLift_coordinates root completion target hdet)
  have hr : (root.1:ℝ) ≠ 0 := by exact_mod_cast hroot
  change (markedMinorIntegerDet target completion:ℝ) +
    (completion.1:ℝ)/(root.1:ℝ)*(markedMinorIntegerDet root target:ℝ) = _
  apply (eq_div_iff hr).mpr
  have heR : (markedMinorIntegerDet target completion:ℝ)*(root.1:ℝ) +
      (markedMinorIntegerDet root target:ℝ)*(completion.1:ℝ) = target.1 := by exact_mod_cast he
  calc
    _ = (markedMinorIntegerDet target completion:ℝ)*(root.1:ℝ) +
        (markedMinorIntegerDet root target:ℝ)*(completion.1:ℝ) := by field_simp
    _ = _ := heR

theorem markedPhysicalRootCoordinates_second (root completion target : ℤ × ℤ) :
    (markedPhysicalRootCoordinates root completion target).2 = markedMinorIntegerDet root target := rfl

theorem markedPhysicalRootCoordinates_divisor (root completion target : ℤ × ℤ)
    {D : ℤ} (hD : D ∣ markedMinorIntegerDet root target) :
    (markedPhysicalRootCoordinates root completion target).2 =
      D*((markedMinorIntegerDet root target)/D) := by
  exact (Int.mul_ediv_cancel' hD).symm

theorem markedPhysicalRootCoordinates_box (root completion target : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) {U : ℝ} (hU : 0 < U)
    (hroot : U ≤ (root.1:ℝ)) (htarget : 0 ≤ (target.1:ℝ)) (htop : (target.1:ℝ) ≤ 16*U) :
    |markedMinorIntegerTau ((completion.1:ℝ)/root.1)
      (markedPhysicalRootCoordinates root completion target)| ≤ 16 := by
  have hp : (0:ℝ)<root.1 := hU.trans_le hroot
  rw [markedPhysicalRootCoordinates_tau root completion target hdet (by exact_mod_cast hp.ne'),
    abs_of_nonneg (div_nonneg htarget hp.le)]
  apply (div_le_iff₀ hp).mpr
  linarith

end
end ArtinMatthews
