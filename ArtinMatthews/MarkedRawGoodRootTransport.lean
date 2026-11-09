module

public import ArtinMatthews.MarkedRawGoodArcAgreement
public import ArtinMatthews.MarkedPhysicalCompletionGood
public import ArtinMatthews.MarkedTypeIITransport


set_option backward.privateInPublic true
@[expose] public section

/-! At every integer root, the original physical good test is exactly
the fixed-coordinate Möbius test used by the continuous path observable. -/

noncomputable section
namespace ArtinMatthews

def markedRootIntegerVector (z : ℤ × ℤ) : Fin 2 → ℝ := ![(z.1:ℝ),(z.2:ℝ)]

theorem markedPhysicalRootLift_det (root completion z w : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) :
    markedMinorIntegerDet (markedPhysicalRootLift root completion z) (markedPhysicalRootLift root completion w) =
      markedMinorIntegerDet z w := by
  calc
    _ = markedMinorIntegerDet root completion*markedMinorIntegerDet z w := by
      unfold markedPhysicalRootLift markedMinorIntegerDet
      ring
    _ = _ := by rw [hdet,one_mul]

theorem markedPhysicalRootLift_first_ratio (root completion z w : ℤ × ℤ)
    (hroot : root.1 ≠ 0) :
    ((markedPhysicalRootLift root completion w).1:ℝ)/((markedPhysicalRootLift root completion z).1:ℝ) =
      markedTransportedRatio ((completion.1:ℝ)/root.1) (markedRootIntegerVector z) (markedRootIntegerVector w) := by
  have hr : (root.1:ℝ) ≠ 0 := by exact_mod_cast hroot
  have hf (v : ℤ × ℤ) : ((markedPhysicalRootLift root completion v).1:ℝ) =
      (root.1:ℝ)*markedTau ((completion.1:ℝ)/root.1) (markedRootIntegerVector v) := by
    simp only [markedPhysicalRootLift,Int.cast_add,Int.cast_mul,markedTau,markedRootIntegerVector,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp
  rw [hf w,hf z,mul_div_mul_left _ _ hr]
  rfl

theorem markedRawDirtyGood_root_lift {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (actualCompletion : Z → ℤ × ℤ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (root completion z w : ℤ × ℤ)
    (hroot : root.1 ≠ 0) (hdet : markedMinorIntegerDet root completion=1)
    (hzw : markedMinorIntegerDet z w=1) (hpos : s.1.1=markedPhysicalRootLift root completion z)
    (hactual : markedMinorIntegerDet s.1.1 (actualCompletion s.1)=1) :
    MarkedRawDirtyGood e x 0 d₀ Y actualCompletion s ↔
      MarkedRawCircleGood e x s.2.1 d₀ Y
        (markedTransportedRatio ((completion.1:ℝ)/root.1) (markedRootIntegerVector z)
          (markedRootIntegerVector w):AddCircle (1:ℝ)) := by
  rw [markedRawDirtyGood_iff_circle]
  simp only [markedMinorIntegerTau,zero_mul,add_zero]
  have hc : markedMinorIntegerDet s.1.1 (markedPhysicalRootLift root completion w)=1 := by
    rw [hpos,markedPhysicalRootLift_det root completion z w hdet,hzw]
  rw [markedPhysical_completion_ratio_circle s.1.1 (markedPhysicalRootLift root completion w)
    (actualCompletion s.1) hc hactual,hpos,markedPhysicalRootLift_first_ratio root completion z w hroot]

end ArtinMatthews
