module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Elementary determinant-one changes of two additive Haar coordinates. -/
namespace ArtinMatthews
open MeasureTheory Matrix
open scoped Classical
noncomputable section

variable {R : Type*} [CommRing R]

def sourceMatrixPairAction (M : Matrix (Fin 2) (Fin 2) R) (x : R × R) : R × R :=
  (M 0 0 * x.1 + M 0 1 * x.2, M 1 0 * x.1 + M 1 1 * x.2)

def sourceSL2Upper (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, t; 0, 1]

def sourceSL2Lower (t : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; t, 1]

def sourceSL2Diagonal (u : Rˣ) : Matrix (Fin 2) (Fin 2) R := !![(u : R), 0; 0, (u⁻¹ : Rˣ)]

theorem sourceMatrixPairAction_mul (M N : Matrix (Fin 2) (Fin 2) R) :
    sourceMatrixPairAction (M * N) = sourceMatrixPairAction M ∘ sourceMatrixPairAction N := by
  funext x
  apply Prod.ext <;> simp only [sourceMatrixPairAction, Matrix.mul_apply, Fin.sum_univ_two,
    Function.comp_apply] <;> ring

theorem sourceSL2Diagonal_factor (u : Rˣ) :
    sourceSL2Diagonal u =
      sourceSL2Upper (u : R) * sourceSL2Lower (-(u⁻¹ : Rˣ) : R) *
        sourceSL2Upper (u : R) * sourceSL2Upper (-1) * sourceSL2Lower 1 * sourceSL2Upper (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceSL2Diagonal, sourceSL2Upper, sourceSL2Lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceSL2_factor_of_unit (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det = 1)
    (u : Rˣ) (hu : M 0 0 = (u : R)) :
    M = sourceSL2Lower (M 1 0 * (u⁻¹ : Rˣ)) * sourceSL2Diagonal u *
      sourceSL2Upper ((u⁻¹ : Rˣ) * M 0 1) := by
  have hd : (u : R) * M 1 1 - M 0 1 * M 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hu] using hM
  have h11 : M 1 1 = (u⁻¹ : Rˣ) * (1 + M 0 1 * M 1 0) := by
    calc
      M 1 1 = (u⁻¹ : Rˣ) * ((u : R) * M 1 1) := by simp
      _ = _ := by congr 1; linear_combination hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceSL2Diagonal, sourceSL2Upper, sourceSL2Lower, Matrix.mul_apply,
      Fin.sum_univ_two, hu, h11]
  all_goals ring

section Measure
variable [MeasurableSpace R] [MeasurableAdd₂ R] [MeasurableMul₂ R]
variable (μ : Measure R) [SFinite μ] [μ.IsAddLeftInvariant]

theorem sourceSL2Lower_measurePreserving (t : R) :
    MeasurePreserving (sourceMatrixPairAction (sourceSL2Lower t)) (μ.prod μ) (μ.prod μ) := by
  change MeasurePreserving (fun x : R × R => (1 * x.1 + 0 * x.2, t * x.1 + 1 * x.2))
    (μ.prod μ) (μ.prod μ)
  have h := (MeasurePreserving.id μ).skew_product
    ((measurable_const.mul measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall fun x : R => map_add_left_eq_self μ (t * x))
  simpa only [one_mul, zero_mul, add_zero, id_eq] using h

theorem sourceSL2Upper_measurePreserving (t : R) :
    MeasurePreserving (sourceMatrixPairAction (sourceSL2Upper t)) (μ.prod μ) (μ.prod μ) := by
  have hs : MeasurePreserving (Prod.swap : R × R → R × R) (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap
  have h := hs.comp ((sourceSL2Lower_measurePreserving μ t).comp hs)
  convert h using 1
  funext x
  apply Prod.ext <;> simp [sourceMatrixPairAction, sourceSL2Upper, sourceSL2Lower, add_comm]

omit [MeasurableAdd₂ R] [MeasurableMul₂ R] [SFinite μ] [μ.IsAddLeftInvariant] in
theorem sourceMatrixPairAction_measurePreserving_mul {M N : Matrix (Fin 2) (Fin 2) R}
    (hM : MeasurePreserving (sourceMatrixPairAction M) (μ.prod μ) (μ.prod μ))
    (hN : MeasurePreserving (sourceMatrixPairAction N) (μ.prod μ) (μ.prod μ)) :
    MeasurePreserving (sourceMatrixPairAction (M * N)) (μ.prod μ) (μ.prod μ) := by
  rw [sourceMatrixPairAction_mul]
  exact hM.comp hN

theorem sourceSL2Diagonal_measurePreserving (u : Rˣ) :
    MeasurePreserving (sourceMatrixPairAction (sourceSL2Diagonal u)) (μ.prod μ) (μ.prod μ) := by
  rw [sourceSL2Diagonal_factor]
  apply sourceMatrixPairAction_measurePreserving_mul μ
  · apply sourceMatrixPairAction_measurePreserving_mul μ
    · apply sourceMatrixPairAction_measurePreserving_mul μ
      · apply sourceMatrixPairAction_measurePreserving_mul μ
        · exact sourceMatrixPairAction_measurePreserving_mul μ
            (sourceSL2Upper_measurePreserving μ _) (sourceSL2Lower_measurePreserving μ _)
        · exact sourceSL2Upper_measurePreserving μ _
      · exact sourceSL2Upper_measurePreserving μ _
    · exact sourceSL2Lower_measurePreserving μ _
  · exact sourceSL2Upper_measurePreserving μ _

theorem sourceSL2_measurePreserving_of_unit_pivot (M : Matrix (Fin 2) (Fin 2) R)
    (hM : M.det = 1) (t : R) (u : Rˣ) (hu : M 0 0 + t * M 1 0 = (u : R)) :
    MeasurePreserving (sourceMatrixPairAction M) (μ.prod μ) (μ.prod μ) := by
  let N := sourceSL2Upper t * M
  have hN : N.det = 1 := by
    dsimp only [N]
    rw [Matrix.det_mul]
    have hU : (sourceSL2Upper t).det = 1 := by simp [sourceSL2Upper, Matrix.det_fin_two]
    rw [hU, hM, one_mul]
  have hNu : N 0 0 = (u : R) := by
    change (sourceSL2Upper t * M) 0 0 = (u : R)
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change 1 * M 0 0 + t * M 1 0 = (u : R)
    simpa only [one_mul] using hu
  have hNm : MeasurePreserving (sourceMatrixPairAction N) (μ.prod μ) (μ.prod μ) := by
    rw [sourceSL2_factor_of_unit N hN u hNu]
    exact sourceMatrixPairAction_measurePreserving_mul μ
      (sourceMatrixPairAction_measurePreserving_mul μ
        (sourceSL2Lower_measurePreserving μ _) (sourceSL2Diagonal_measurePreserving μ _))
      (sourceSL2Upper_measurePreserving μ _)
  have hcancel : sourceSL2Upper (-t) * N = M := by
    dsimp only [N]
    rw [← Matrix.mul_assoc]
    have h : sourceSL2Upper (-t) * sourceSL2Upper t = (1 : Matrix (Fin 2) (Fin 2) R) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sourceSL2Upper, Matrix.mul_apply, Fin.sum_univ_two]
    rw [h, one_mul]
  rw [← hcancel]
  exact sourceMatrixPairAction_measurePreserving_mul μ
    (sourceSL2Upper_measurePreserving μ _) hNm

end Measure
end
end ArtinMatthews
