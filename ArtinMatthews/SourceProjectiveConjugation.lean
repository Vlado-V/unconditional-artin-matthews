module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Units


set_option backward.privateInPublic true
@[expose] public section

/-! Faithful finite conjugation coordinates for the actual projective group. -/
namespace ArtinMatthews
open Matrix Topology
open scoped MatrixGroups
noncomputable section

abbrev SourceConjugationIndex := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

def sourceGLConjugationCoordinates {R : Type*} [CommRing R]
    (g : GL (Fin 2) R) (p : SourceConjugationIndex) : R :=
  (g.val * Matrix.single p.1.1 p.1.2 (1 : R) * (g⁻¹).val :
    Matrix (Fin 2) (Fin 2) R) p.2.1 p.2.2

theorem sourceGLConjugationCoordinates_scalar {R : Type*} [CommRing R]
    (g : GL (Fin 2) R) (u : Rˣ) :
    sourceGLConjugationCoordinates (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceGLConjugationCoordinates g := by
  funext p
  let c := GeneralLinearGroup.scalar (Fin 2) u
  have hc : c.val * Matrix.single p.1.1 p.1.2 (1 : R) =
      Matrix.single p.1.1 p.1.2 (1 : R) * c.val :=
    Matrix.scalar_comm (u : R) (Commute.all _) _
  have he : (g * c).val * Matrix.single p.1.1 p.1.2 (1 : R) * ((g * c)⁻¹).val =
      g.val * Matrix.single p.1.1 p.1.2 (1 : R) * (g⁻¹).val := by
    simp only [_root_.mul_inv_rev, Units.val_mul]
    calc
      _ = g.val * (c.val * Matrix.single p.1.1 p.1.2 (1 : R)) * (c⁻¹).val * (g⁻¹).val := by
        simp only [Matrix.mul_assoc]
      _ = g.val * (Matrix.single p.1.1 p.1.2 (1 : R) * c.val) * (c⁻¹).val * (g⁻¹).val := by
        rw [hc]
      _ = _ := by simp [Matrix.mul_assoc]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M p.2.1 p.2.2) he

def sourceProjectiveConjugationCoordinates {R : Type*} [CommRing R] :
    PGL(2, R) → SourceConjugationIndex → R :=
  Quotient.lift sourceGLConjugationCoordinates (by
    intro g h hgh
    have he : ProjGenLinGroup.mk g = ProjGenLinGroup.mk h := Quotient.sound hgh
    obtain ⟨u, rfl⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    exact (sourceGLConjugationCoordinates_scalar g u).symm)

@[simp] theorem sourceProjectiveConjugationCoordinates_mk {R : Type*} [CommRing R]
    (g : GL (Fin 2) R) :
    sourceProjectiveConjugationCoordinates (ProjGenLinGroup.mk g) =
      sourceGLConjugationCoordinates g := rfl

theorem sourceProjectiveConjugationCoordinates_injective {R : Type*} [CommRing R] :
    Function.Injective (sourceProjectiveConjugationCoordinates (R := R)) := by
  intro g h he
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    induction h using ProjGenLinGroup.induction_on with
    | mk h =>
      apply ProjGenLinGroup.mk_eq_mk_iff'.mpr
      refine ⟨g⁻¹ * h, ?_, by simp⟩
      apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      apply Matrix.mem_range_scalar_of_commute_single
      intro i j _
      apply Commute.symm
      have hc : g.val * Matrix.single i j 1 * (g⁻¹).val =
          h.val * Matrix.single i j 1 * (h⁻¹).val := by
        ext k l
        exact congrFun he ((i,j),(k,l))
      change (g⁻¹ * h).val * Matrix.single i j 1 =
        Matrix.single i j 1 * (g⁻¹ * h).val
      calc
        _ = (g⁻¹).val * (h.val * Matrix.single i j 1 * (h⁻¹).val) * h.val := by
          simp [Matrix.mul_assoc]
        _ = (g⁻¹).val * (g.val * Matrix.single i j 1 * (g⁻¹).val) * h.val := by rw [← hc]
        _ = _ := by simp [Matrix.mul_assoc]


theorem sourceGLConjugationCoordinates_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : GL (Fin 2) R) :
    sourceGLConjugationCoordinates (GeneralLinearGroup.map f g) =
      fun p => f (sourceGLConjugationCoordinates g p) := by
  funext p
  simp only [sourceGLConjugationCoordinates, ← map_inv]
  change (g.val.map f * Matrix.single p.1.1 p.1.2 (1 : S) * (g⁻¹).val.map f :
    Matrix (Fin 2) (Fin 2) S) p.2.1 p.2.2 = _
  rw [← f.map_one, ← Matrix.map_single, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

theorem sourceProjectiveConjugationCoordinates_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : PGL(2, R)) :
    sourceProjectiveConjugationCoordinates (ProjGenLinGroup.map f g) =
      fun p => f (sourceProjectiveConjugationCoordinates g p) := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => exact sourceGLConjugationCoordinates_map f g

section Topology
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local instance : TopologicalSpace (PGL(2, R)) :=
  inferInstanceAs (TopologicalSpace (GL (Fin 2) R ⧸ Subgroup.center (GL (Fin 2) R)))

theorem sourceGLConjugationCoordinates_continuous :
    Continuous (sourceGLConjugationCoordinates (R := R)) := by
  have hv : Continuous (fun g : GL (Fin 2) R => g.val) := Units.continuous_val
  apply continuous_pi
  intro p
  exact ((hv.mul continuous_const).mul (hv.comp continuous_inv)).matrix_elem p.2.1 p.2.2

theorem sourceProjectiveConjugationCoordinates_continuous :
    Continuous (sourceProjectiveConjugationCoordinates (R := R)) :=
  sourceGLConjugationCoordinates_continuous.quotient_lift _

end Topology

end
end ArtinMatthews
