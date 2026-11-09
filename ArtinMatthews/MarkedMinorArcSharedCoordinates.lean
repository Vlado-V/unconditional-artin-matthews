module

public import ArtinMatthews.MarkedMinorArcCellGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical actual shared-lattice coordinates, including exact scaled
determinant transport. -/
namespace ArtinMatthews

/-- Literal coordinates in Z*z+Z*D*w; divisibility will be proved from the
actual preserved prime-line tuple. -/
def markedMinorSharedCoordinates (D : ℕ) (z w v : ℤ × ℤ) : ℤ × ℤ :=
  (markedMinorIntegerDet v w,markedMinorIntegerDet z v/(D : ℤ))

theorem markedMinorSharedCoordinates_decompose {D : ℕ} (hD : D ≠ 0)
    (z w v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hv : (D : ℤ) ∣ markedMinorIntegerDet z v) :
    v.1=(markedMinorSharedCoordinates D z w v).1*z.1+
      (D : ℤ)*(markedMinorSharedCoordinates D z w v).2*w.1 ∧
    v.2=(markedMinorSharedCoordinates D z w v).1*z.2+
      (D : ℤ)*(markedMinorSharedCoordinates D z w v).2*w.2 := by
  obtain ⟨l,hl⟩ := hv
  have hDn : (D : ℤ) ≠ 0 := by exact_mod_cast hD
  have hj : markedMinorIntegerDet z v/(D : ℤ)=l := by
    rw [hl,Int.mul_ediv_cancel_left _ hDn]
  have hb := markedMinorIntegerBasis_decompose z w v hd
  rw [hl] at hb
  simpa only [markedMinorSharedCoordinates,hj] using hb

/-- On the genuine shared lattice, the canonical coordinates are injective. -/
theorem markedMinorSharedCoordinates_inj {D : ℕ} (hD : D ≠ 0)
    (z w u v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hu : (D : ℤ) ∣ markedMinorIntegerDet z u) (hv : (D : ℤ) ∣ markedMinorIntegerDet z v)
    (he : markedMinorSharedCoordinates D z w u=markedMinorSharedCoordinates D z w v) : u=v := by
  have h₁ := markedMinorSharedCoordinates_decompose hD z w u hd hu
  have h₂ := markedMinorSharedCoordinates_decompose hD z w v hd hv
  rw [he] at h₁
  exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)

/-- The actual position determinant divided by the shared product D is
exactly the ordinary determinant in the canonical integer coordinates. -/
theorem markedMinorSharedCoordinates_determinant {D : ℕ} (hD : D ≠ 0)
    (z w u v : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hu : (D : ℤ) ∣ markedMinorIntegerDet z u) (hv : (D : ℤ) ∣ markedMinorIntegerDet z v) :
    markedMinorIntegerDet u v/(D : ℤ)=markedMinorIntegerDet
      (markedMinorSharedCoordinates D z w u) (markedMinorSharedCoordinates D z w v) := by
  have h₁ := markedMinorSharedCoordinates_decompose hD z w u hd hu
  have h₂ := markedMinorSharedCoordinates_decompose hD z w v hd hv
  have he : markedMinorIntegerDet u v=(D : ℤ)*markedMinorIntegerDet
      (markedMinorSharedCoordinates D z w u) (markedMinorSharedCoordinates D z w v)*
        markedMinorIntegerDet z w := by
    unfold markedMinorIntegerDet
    rw [h₁.1,h₁.2,h₂.1,h₂.2]
    ring
  rw [he,hd,mul_one,Int.mul_ediv_cancel_left _ (by exact_mod_cast hD : (D : ℤ)≠0)]

end ArtinMatthews
