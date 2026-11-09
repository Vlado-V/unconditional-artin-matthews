module

public import ArtinMatthews.MarkedMinorArcSharedLattice


set_option backward.privateInPublic true
@[expose] public section

/-! Actual source cells and the sheared coordinates in the shared lattice. -/
namespace ArtinMatthews

/-- The actual real linear form used by the root transport. -/
def markedMinorIntegerTau (r : ℝ) (z : ℤ × ℤ) : ℝ := (z.1 : ℝ)+r*(z.2 : ℝ)

/-- Exact cross-ratio difference controlling connected source cells. -/
theorem markedMinorIntegerTau_difference (r : ℝ) (z v : ℤ × ℤ)
    (hz : markedMinorIntegerTau r z ≠ 0) (hv : markedMinorIntegerTau r v ≠ 0) :
    (v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z =
      (markedMinorIntegerDet z v : ℝ)/(markedMinorIntegerTau r z*markedMinorIntegerTau r v) := by
  field_simp [hz,hv]
  unfold markedMinorIntegerDet markedMinorIntegerTau
  push_cast
  ring

/-- Actual shared-lattice coordinates give the source shear parameter
D*tau(w)/tau(z), including the determinant normalization D. -/
theorem markedMinorSharedLattice_shear (r : ℝ) (D : ℕ) (z w v : ℤ × ℤ)
    (h l : ℤ) (h₁ : v.1=h*z.1+(D : ℤ)*l*w.1) (h₂ : v.2=h*z.2+(D : ℤ)*l*w.2)
    (hz : markedMinorIntegerTau r z ≠ 0) :
    (h : ℝ)+(l : ℝ)*((D : ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z) =
      markedMinorIntegerTau r v/markedMinorIntegerTau r z := by
  unfold markedMinorIntegerTau at *
  rw [h₁,h₂]
  push_cast
  field_simp
  ring

/-- Actual integer shared-lattice coordinates have determinant D*l. -/
theorem markedMinorSharedLattice_determinant (D : ℕ) (z w v : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1) (h l : ℤ)
    (h₁ : v.1=h*z.1+(D : ℤ)*l*w.1) (h₂ : v.2=h*z.2+(D : ℤ)*l*w.2) :
    markedMinorIntegerDet z v=(D : ℤ)*l := by
  unfold markedMinorIntegerDet at hd ⊢
  rw [h₁,h₂]
  linear_combination (D : ℤ)*l*hd

/-- The exact source box and cell hypotheses imply the actual sheared-region
bounds. No sheared support bound is assumed as an input. -/
theorem markedMinorSharedLattice_cell_bounds (r : ℝ) {Y c B R : ℝ}
    (hY : 0 < Y) (hc : 0 < c) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (D : ℕ) (hD : 0 < D) (z w v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (h l : ℤ) (h₁ : v.1=h*z.1+(D : ℤ)*l*w.1) (h₂ : v.2=h*z.2+(D : ℤ)*l*w.2)
    (hzlo : c ≤ |markedMinorIntegerTau r z|) (hzhi : |markedMinorIntegerTau r z| ≤ B)
    (hvlo : c ≤ |markedMinorIntegerTau r v|) (hvhi : |markedMinorIntegerTau r v| ≤ B)
    (hcell : |(v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z| ≤ R*D*Y) :
    |(h : ℝ)+(l : ℝ)*((D : ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z)| ≤ B/c ∧
      |(l : ℝ)/Y| ≤ R*B^2 := by
  have hz : markedMinorIntegerTau r z ≠ 0 := abs_pos.mp (hc.trans_le hzlo)
  have hv : markedMinorIntegerTau r v ≠ 0 := abs_pos.mp (hc.trans_le hvlo)
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  constructor
  · rw [markedMinorSharedLattice_shear r D z w v h l h₁ h₂ hz,abs_div]
    exact (div_le_div_of_nonneg_right hvhi (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left hB hc hzlo)
  · have hdet := markedMinorSharedLattice_determinant D z w v hd h l h₁ h₂
    have hid : (l : ℝ)/Y =
        ((v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z)*
          (markedMinorIntegerTau r z*markedMinorIntegerTau r v)/((D : ℝ)*Y) := by
      rw [markedMinorIntegerTau_difference r z v hz hv,hdet]
      push_cast
      field_simp
    rw [hid,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos hDr,abs_of_pos hY]
    calc
      _ ≤ ((R*D*Y)*(B*B))/((D : ℝ)*Y) := by gcongr
      _ = _ := by field_simp

end ArtinMatthews
