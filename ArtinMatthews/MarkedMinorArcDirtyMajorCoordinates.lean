module

public import ArtinMatthews.MarkedMinorArcSharedCoordinates
public import ArtinMatthews.MarkedMinorArcLatticeCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Literal determinant-D reduced basis and its integer coordinates. -/
namespace ArtinMatthews

 def markedDirtyMajorLatticeVector (D : ℕ) (z w c : ℤ × ℤ) : ℤ × ℤ :=
  (c.1*z.1+(D:ℤ)*c.2*w.1,c.1*z.2+(D:ℤ)*c.2*w.2)

 def markedDirtyMajorReducedCoordinates (D : ℕ) (z w : ℤ × ℤ) (h l a b : ℤ)
    (v : ℤ × ℤ) : ℤ × ℤ :=
  markedMinorBasisCoords h l a b (markedMinorSharedCoordinates D z w v)

 theorem markedDirtyMajor_lattice_basis_det (D : ℕ) (z w : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1) (h l a b : ℤ) (hb : h*b-l*a=1) :
    markedMinorIntegerDet (markedDirtyMajorLatticeVector D z w (h,l))
      (markedDirtyMajorLatticeVector D z w (a,b))=(D:ℤ) := by
  unfold markedDirtyMajorLatticeVector markedMinorIntegerDet at *
  dsimp only at *
  calc
    _ = (D:ℤ)*(h*b-l*a)*(z.1*w.2-z.2*w.1) := by ring
    _ = _ := by rw [hd,hb,mul_one,mul_one]

 theorem markedDirtyMajor_reduced_decompose {D : ℕ} (hD : D ≠ 0) (z w v : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1) (h l a b : ℤ) (hb : h*b-l*a=1)
    (hv : (D:ℤ) ∣ markedMinorIntegerDet z v) :
    v.1=(markedDirtyMajorReducedCoordinates D z w h l a b v).1*
      (markedDirtyMajorLatticeVector D z w (h,l)).1+
      (markedDirtyMajorReducedCoordinates D z w h l a b v).2*
      (markedDirtyMajorLatticeVector D z w (a,b)).1 ∧
    v.2=(markedDirtyMajorReducedCoordinates D z w h l a b v).1*
      (markedDirtyMajorLatticeVector D z w (h,l)).2+
      (markedDirtyMajorReducedCoordinates D z w h l a b v).2*
      (markedDirtyMajorLatticeVector D z w (a,b)).2 := by
  have hvv := markedMinorSharedCoordinates_decompose hD z w v hd hv
  have hcc := markedMinorBasisCoords_inverse h l a b hb (markedMinorSharedCoordinates D z w v)
  constructor
  · calc
      _ = (markedMinorSharedCoordinates D z w v).1*z.1+
          (D:ℤ)*(markedMinorSharedCoordinates D z w v).2*w.1 := hvv.1
      _ = _ := by
        rw [← hcc.1,← hcc.2]
        dsimp only [markedDirtyMajorReducedCoordinates,markedDirtyMajorLatticeVector]
        ring
  · calc
      _ = (markedMinorSharedCoordinates D z w v).1*z.2+
          (D:ℤ)*(markedMinorSharedCoordinates D z w v).2*w.2 := hvv.2
      _ = _ := by
        rw [← hcc.1,← hcc.2]
        dsimp only [markedDirtyMajorReducedCoordinates,markedDirtyMajorLatticeVector]
        ring

 theorem markedDirtyMajor_reduced_injective {D : ℕ} (hD : D ≠ 0) (z w : ℤ × ℤ)
    (hd : markedMinorIntegerDet z w=1) (h l a b : ℤ) (hb : h*b-l*a=1)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V,(D:ℤ) ∣ markedMinorIntegerDet z v) :
    Set.InjOn (markedDirtyMajorReducedCoordinates D z w h l a b) ↑V := by
  intro u hu v hv heq
  exact markedMinorSharedCoordinates_inj hD z w u v hd (hV u hu) (hV v hv)
    (markedMinorBasisCoords_injective h l a b hb heq)

end ArtinMatthews
