module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual projective linear group over a product ring is the
product of the projective linear groups. Scalar representatives
reassemble from their two genuine unit components. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceKPUnitPair {R T : Type*} [Monoid R] [Monoid T] (x : Rˣ) (y : Tˣ) : (R × T)ˣ :=
  ⟨((x : R), (y : T)), (((x⁻¹ : Rˣ) : R), ((y⁻¹ : Tˣ) : T)),
    Prod.ext x.val_inv y.val_inv, Prod.ext x.inv_val y.inv_val⟩

variable (R T : Type*) [CommRing R] [CommRing T]

def sourceKPGL2ProductMap : GL (Fin 2) (R × T) →* GL (Fin 2) R × GL (Fin 2) T :=
  (GeneralLinearGroup.map (RingHom.fst R T)).prod (GeneralLinearGroup.map (RingHom.snd R T))

theorem sourceKPGL2ProductMap_injective : Function.Injective (sourceKPGL2ProductMap R T) := by
  intro g h he
  apply GeneralLinearGroup.ext
  intro i j
  exact Prod.ext (congrArg (fun a : GL (Fin 2) R × GL (Fin 2) T => a.1 i j) he)
    (congrArg (fun a : GL (Fin 2) R × GL (Fin 2) T => a.2 i j) he)

theorem sourceKPGL2ProductMap_surjective : Function.Surjective (sourceKPGL2ProductMap R T) := by
  rintro ⟨g, h⟩
  let A : Matrix (Fin 2) (Fin 2) (R × T) := fun i j => (g i j, h i j)
  have hdet : A.det = ((GeneralLinearGroup.det g : R), (GeneralLinearGroup.det h : T)) := by
    apply Prod.ext
    · change A.det.1 = (GeneralLinearGroup.det g : R)
      rw [Matrix.det_fin_two, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      rfl
    · change A.det.2 = (GeneralLinearGroup.det h : T)
      rw [Matrix.det_fin_two, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      rfl
  let a := GeneralLinearGroup.mk'' A ⟨sourceKPUnitPair (GeneralLinearGroup.det g) (GeneralLinearGroup.det h), hdet.symm⟩
  refine ⟨a, Prod.ext ?_ ?_⟩
  · apply GeneralLinearGroup.ext
    intro i j
    rfl
  · apply GeneralLinearGroup.ext
    intro i j
    rfl

def sourceKPProjectiveProductMap : PGL(2, R × T) →* PGL(2, R) × PGL(2, T) :=
  (ProjGenLinGroup.map (RingHom.fst R T)).prod (ProjGenLinGroup.map (RingHom.snd R T))

theorem sourceKPProjectiveProductMap_injective : Function.Injective (sourceKPProjectiveProductMap R T) := by
  intro x y h
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  obtain ⟨k, rfl⟩ := ProjGenLinGroup.mk_surjective y
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  let p : GL (Fin 2) (R × T) →* GL (Fin 2) R := GeneralLinearGroup.map (RingHom.fst R T)
  let q : GL (Fin 2) (R × T) →* GL (Fin 2) T := GeneralLinearGroup.map (RingHom.snd R T)
  change ProjGenLinGroup.mk (p g) = ProjGenLinGroup.mk (p k) at h₁
  change ProjGenLinGroup.mk (q g) = ProjGenLinGroup.mk (q k) at h₂
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h₁
  obtain ⟨v, hv⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h₂
  let a := sourceKPUnitPair u v
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨a, sourceKPGL2ProductMap_injective R T (Prod.ext ?_ ?_)⟩
  · change p (g * GeneralLinearGroup.scalar (Fin 2) a) = p k
    rw [map_mul p]
    have hs : p (GeneralLinearGroup.scalar (Fin 2) a) = GeneralLinearGroup.scalar (Fin 2) u := by
      change GeneralLinearGroup.map (RingHom.fst R T) (GeneralLinearGroup.scalar (Fin 2) a) = _
      rw [GeneralLinearGroup.map_scalar]
      exact congrArg (GeneralLinearGroup.scalar (Fin 2)) (Units.ext rfl)
    rw [hs]
    exact hu
  · change q (g * GeneralLinearGroup.scalar (Fin 2) a) = q k
    rw [map_mul q]
    have hs : q (GeneralLinearGroup.scalar (Fin 2) a) = GeneralLinearGroup.scalar (Fin 2) v := by
      change GeneralLinearGroup.map (RingHom.snd R T) (GeneralLinearGroup.scalar (Fin 2) a) = _
      rw [GeneralLinearGroup.map_scalar]
      exact congrArg (GeneralLinearGroup.scalar (Fin 2)) (Units.ext rfl)
    rw [hs]
    exact hv

theorem sourceKPProjectiveProductMap_surjective : Function.Surjective (sourceKPProjectiveProductMap R T) := by
  rintro ⟨x, y⟩
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := ProjGenLinGroup.mk_surjective y
  obtain ⟨k, hk⟩ := sourceKPGL2ProductMap_surjective R T (g, h)
  refine ⟨ProjGenLinGroup.mk k, ?_⟩
  exact congrArg (fun a : GL (Fin 2) R × GL (Fin 2) T => (ProjGenLinGroup.mk a.1, ProjGenLinGroup.mk a.2)) hk

def sourceKPProjectiveProductEquiv : PGL(2, R × T) ≃* PGL(2, R) × PGL(2, T) :=
  MulEquiv.ofBijective (sourceKPProjectiveProductMap R T)
    ⟨sourceKPProjectiveProductMap_injective R T, sourceKPProjectiveProductMap_surjective R T⟩

end
end ArtinMatthews
