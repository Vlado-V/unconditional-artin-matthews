module

public import ArtinMatthews.SourceProjectiveBruhat
public import ArtinMatthews.SourceKubotaGL2Generation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Normalized diagonals over the actual adele rings. The projective
diagonal coordinate is injective over a commutative ring, and a rational
projective matrix which becomes diagonal has a rational diagonal ratio. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceKPDiagonalHom (R : Type*) [CommRing R] : Rˣ →* GL (Fin 2) R where
  toFun u := GeneralLinearGroup.mk'' !![(u : R), 0; 0, 1] (by simp [Matrix.det_fin_two])
  map_one' := by
    apply GeneralLinearGroup.ext
    intro i j
    change (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) R) i j = (1 : Matrix (Fin 2) (Fin 2) R) i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    apply GeneralLinearGroup.ext
    intro i j
    change (!![(u : R) * (v : R), 0; 0, 1] : Matrix (Fin 2) (Fin 2) R) i j =
      (!![(u : R), 0; 0, 1] * !![(v : R), 0; 0, 1]) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKPDiagonalHom_field {F : Type*} [Field F] (u : Fˣ) :
    sourceKPDiagonalHom F u = sourceGL2Diagonal u := by
  apply Units.ext
  rfl

theorem sourceKPDiagonalHom_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (u : Rˣ) :
    GeneralLinearGroup.map f (sourceKPDiagonalHom R u) =
      sourceKPDiagonalHom T (Units.map f.toMonoidHom u) := by
  apply GeneralLinearGroup.ext
  intro i j
  change f ((!![(u : R), 0; 0, 1] : Matrix (Fin 2) (Fin 2) R) i j) =
    (!![f (u : R), 0; 0, 1] : Matrix (Fin 2) (Fin 2) T) i j
  fin_cases i <;> fin_cases j <;> simp

theorem sourceKPMatrix_right_scalar_entry {R : Type*} [CommRing R] (g : GL (Fin 2) R)
    (u : Rˣ) (i j : Fin 2) :
    (g * GeneralLinearGroup.scalar (Fin 2) u) i j = g i j * (u : R) := by
  exact Matrix.mul_diagonal (fun _ : Fin 2 => (u : R)) (g : Matrix (Fin 2) (Fin 2) R) i j

def sourceKPProjectiveDiagonalHom (R : Type*) [CommRing R] : Rˣ →* PGL(2, R) :=
  ProjGenLinGroup.mk.comp (sourceKPDiagonalHom R)

theorem sourceKPProjectiveDiagonalHom_injective (R : Type*) [CommRing R] :
    Function.Injective (sourceKPProjectiveDiagonalHom R) := by
  intro u v h
  change ProjGenLinGroup.mk (sourceKPDiagonalHom R u) = ProjGenLinGroup.mk (sourceKPDiagonalHom R v) at h
  obtain ⟨w, hw⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h11 := congrArg (fun g : GL (Fin 2) R => g 1 1) hw
  rw [sourceKPMatrix_right_scalar_entry] at h11
  change (1 : R) * (w : R) = 1 at h11
  have he : w = 1 := Units.ext (by simpa only [one_mul, Units.val_one] using h11)
  subst w
  rw [map_one, mul_one] at hw
  exact Units.ext (congrArg (fun g : GL (Fin 2) R => g 0 0) hw)

theorem sourceKPProjectiveDiagonalHom_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (u : Rˣ) :
    ProjGenLinGroup.map f (sourceKPProjectiveDiagonalHom R u) =
      sourceKPProjectiveDiagonalHom T (Units.map f.toMonoidHom u) := by
  change ProjGenLinGroup.mk (GeneralLinearGroup.map f (sourceKPDiagonalHom R u)) = _
  rw [sourceKPDiagonalHom_map]
  rfl

theorem sourceKPProjectiveDiagonalHom_rational {F R : Type*} [Field F] [CommRing R] [Nontrivial R]
    (f : F →+* R) (g : PGL(2, F)) (u : Rˣ)
    (h : ProjGenLinGroup.map f g = sourceKPProjectiveDiagonalHom R u) :
    ∃ y : Fˣ, g = sourceKPProjectiveDiagonalHom F y ∧ u = Units.map f.toMonoidHom y := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    have hh : ProjGenLinGroup.mk (GeneralLinearGroup.map f g) = ProjGenLinGroup.mk (sourceKPDiagonalHom R u) := h
    obtain ⟨w, hw⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hh
    have hoff (i j : Fin 2) (hij : i ≠ j) : g i j = 0 := by
      have he := congrArg (fun a : GL (Fin 2) R => a i j) hw
      rw [sourceKPMatrix_right_scalar_entry] at he
      have hd : sourceKPDiagonalHom R u i j = 0 := by
        fin_cases i <;> fin_cases j <;> simp_all [sourceKPDiagonalHom]
      change f (g i j) * (w : R) = sourceKPDiagonalHom R u i j at he
      rw [hd] at he
      have hc := congrArg (fun t : R => t * (((w⁻¹ : Rˣ)) : R)) he
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, zero_mul] at hc
      exact f.injective (hc.trans f.map_zero.symm)
    obtain ⟨x, y, d, hfactor⟩ := sourceGL2_triangular_factor g (hoff 1 0 (by decide))
    have hx : x = 0 := by
      have he := congrArg (fun a : GL (Fin 2) F => a 0 1) hfactor
      change g 0 1 = (sourceGL2Upper x * sourceGL2Diagonal y * GeneralLinearGroup.scalar (Fin 2) d) 0 1 at he
      rw [hoff 0 1 (by decide), sourceKPMatrix_right_scalar_entry] at he
      have h01 : (sourceGL2Upper x * sourceGL2Diagonal y) 0 1 = x := by
        simp [sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two]
      rw [h01] at he
      exact (mul_eq_zero.mp he.symm).resolve_right d.ne_zero
    have hg : ProjGenLinGroup.mk g = sourceKPProjectiveDiagonalHom F y := by
      rw [hfactor, hx, sourceGL2Upper_zero, one_mul, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
      exact congrArg ProjGenLinGroup.mk (sourceKPDiagonalHom_field y).symm
    refine ⟨y, hg, sourceKPProjectiveDiagonalHom_injective R ?_⟩
    rw [← sourceKPProjectiveDiagonalHom_map, ← hg]
    exact h.symm

end
end ArtinMatthews
