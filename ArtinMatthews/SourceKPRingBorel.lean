module

public import ArtinMatthews.SourceKPAdelicUpper
public import ArtinMatthews.SourceKPRationalBruhat
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Normalized Borel coordinates over the actual commutative adele
rings. The upper and diagonal coordinates are unique after quotienting
ordinary scalar matrices. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

variable (R : Type*) [CommRing R]

def sourceKPRingNormalizedBorel : Subgroup (GL (Fin 2) R) where
  carrier := {g | g 1 0 = 0 ∧ g 1 1 = 1}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg0, hg1⟩ ⟨hh0, hh1⟩
    constructor <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, hh0, hh1]
  inv_mem' := by
    rintro g ⟨hg0, hg1⟩
    have he0 := congrArg (fun a : GL (Fin 2) R => a 1 0) (mul_inv_cancel g)
    have he1 := congrArg (fun a : GL (Fin 2) R => a 1 1) (mul_inv_cancel g)
    change ((g : Matrix (Fin 2) (Fin 2) R) * (g⁻¹ : GL (Fin 2) R)) 1 0 = 0 at he0
    change ((g : Matrix (Fin 2) (Fin 2) R) * (g⁻¹ : GL (Fin 2) R)) 1 1 = 1 at he1
    constructor
    · simpa only [Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, zero_mul, one_mul, zero_add] using he0
    · simpa only [Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, zero_mul, one_mul, zero_add] using he1

theorem sourceKPRingNormalizedBorel_upper (x : R) :
    sourceKPUpperMatrix R x ∈ sourceKPRingNormalizedBorel R := by
  constructor <;> rfl

theorem sourceKPRingNormalizedBorel_diagonal (a : Rˣ) :
    sourceKPDiagonalHom R a ∈ sourceKPRingNormalizedBorel R := by
  constructor <;> rfl

theorem sourceKPRingNormalizedBorel_factor (g : GL (Fin 2) R)
    (hg : g ∈ sourceKPRingNormalizedBorel R) :
    g = sourceKPUpperMatrix R (g 0 1) * sourceKPDiagonalHom R (GeneralLinearGroup.det g) := by
  have hdet : (GeneralLinearGroup.det g : R) = g 0 0 := by
    change Matrix.det (g : Matrix (Fin 2) (Fin 2) R) = g 0 0
    rw [Matrix.det_fin_two, hg.1, hg.2, mul_one, mul_zero, sub_zero]
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceKPUpperMatrix, sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two,
      hg.1, hg.2, hdet]

def sourceKPRingBorel : Subgroup PGL(2, R) :=
  (sourceKPRingNormalizedBorel R).map ProjGenLinGroup.mk

theorem sourceKPRingBorel_mem_iff (g : PGL(2, R)) :
    g ∈ sourceKPRingBorel R ↔ ∃ (x : R) (a : Rˣ),
      g = ProjGenLinGroup.mk (sourceKPUpperMatrix R x) * sourceKPProjectiveDiagonalHom R a := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b 0 1, GeneralLinearGroup.det b, ?_⟩
    calc
      _ = ProjGenLinGroup.mk
          (sourceKPUpperMatrix R (b 0 1) * sourceKPDiagonalHom R (GeneralLinearGroup.det b)) :=
        congrArg ProjGenLinGroup.mk (sourceKPRingNormalizedBorel_factor R b hb)
      _ = _ := map_mul ProjGenLinGroup.mk _ _
  · rintro ⟨x, a, rfl⟩
    refine ⟨sourceKPUpperMatrix R x * sourceKPDiagonalHom R a,
      (sourceKPRingNormalizedBorel R).mul_mem
        (sourceKPRingNormalizedBorel_upper R x) (sourceKPRingNormalizedBorel_diagonal R a), ?_⟩
    exact map_mul ProjGenLinGroup.mk _ _

theorem sourceKPRingBorel_coordinates_injective : Function.Injective
    (fun p : R × Rˣ => ProjGenLinGroup.mk (sourceKPUpperMatrix R p.1) *
      sourceKPProjectiveDiagonalHom R p.2) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ he
  change ProjGenLinGroup.mk (sourceKPUpperMatrix R x) * ProjGenLinGroup.mk (sourceKPDiagonalHom R a) =
    ProjGenLinGroup.mk (sourceKPUpperMatrix R y) * ProjGenLinGroup.mk (sourceKPDiagonalHom R b) at he
  rw [← map_mul, ← map_mul] at he
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  have h11 := congrArg (fun g : GL (Fin 2) R => g 1 1) hu
  have hu1 : u = 1 := by
    apply Units.ext
    simpa [sourceKPMatrix_right_scalar_entry, sourceKPUpperMatrix, sourceKPDiagonalHom,
      Matrix.mul_apply, Fin.sum_univ_two] using h11
  rw [hu1, map_one, mul_one] at hu
  have h01 := congrArg (fun g : GL (Fin 2) R => g 0 1) hu
  have h00 := congrArg (fun g : GL (Fin 2) R => g 0 0) hu
  apply Prod.ext
  · simpa [sourceKPUpperMatrix, sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two] using h01
  · apply Units.ext
    simpa [sourceKPUpperMatrix, sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two] using h00

theorem sourceKPRingBorel_field {F : Type*} [Field F] :
    sourceKPRingBorel F = sourceKPRationalBorel F := rfl

end
end ArtinMatthews
