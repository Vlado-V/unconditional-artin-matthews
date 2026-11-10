module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.LinearAlgebra.Matrix.Permutation
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! # Elementary Matrix Units -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryMatrixUnits.CM

noncomputable section

/-! Elementary row operations belong to every subgroup containing
all symmetric invertible matrices. This algebra works over commutative rings. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

def swapUnit (i j : I) : (Matrix I I R)ˣ where
  val := (Equiv.swap i j).permMatrix R
  inv := (Equiv.swap i j).permMatrix R
  val_inv := by rw [← Matrix.permMatrix_mul]; simp
  inv_val := by rw [← Matrix.permMatrix_mul]; simp

theorem swapUnit_symmetric (i j : I) : (swapUnit (R := R) i j).val.IsSymm := by
  change ((Equiv.swap i j).permMatrix R).transpose = (Equiv.swap i j).permMatrix R
  rw [Matrix.transpose_permMatrix]
  simp

theorem swapUnit_square (i j : I) : swapUnit (R := R) i j * swapUnit i j = 1 := by
  apply Units.ext
  change (Equiv.swap i j).permMatrix R * (Equiv.swap i j).permMatrix R = 1
  rw [← Matrix.permMatrix_mul]
  simp

theorem transvection_mul_swap (t : Matrix.TransvectionStruct I R) :
    t.toMatrix * (swapUnit t.i t.j).val =
      (swapUnit t.i t.j).val + Matrix.single t.i t.i t.c := by
  rw [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mul, Matrix.one_mul]
  congr 1
  ext a b
  by_cases ha : a = t.i
  · subst a
    rw [Matrix.single_mul_apply_same]
    simp [swapUnit, PEquiv.toMatrix, Equiv.toPEquiv_apply, Matrix.single]
  · rw [Matrix.single_mul_apply_of_ne t.c t.i t.j a b ha]
    simp [Matrix.single, Ne.symm ha]

theorem transvection_mul_swap_symmetric (t : Matrix.TransvectionStruct I R) :
    (t.toMatrix * (swapUnit t.i t.j).val).IsSymm := by
  rw [transvection_mul_swap]
  apply (swapUnit_symmetric t.i t.j).add
  change (Matrix.single t.i t.i t.c).transpose = Matrix.single t.i t.i t.c
  simp

def transvectionUnit (t : TransvectionStruct I R) : (Matrix I I R)ˣ where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := t.mul_inv
  inv_val := t.inv_mul

theorem transvection_mem (H : Subgroup (Matrix I I R)ˣ)
    (hSym : ∀ A : (Matrix I I R)ˣ, A.val.IsSymm → A ∈ H)
    (t : TransvectionStruct I R) : transvectionUnit t ∈ H := by
  have hAP : transvectionUnit t * swapUnit t.i t.j ∈ H :=
    hSym _ (transvection_mul_swap_symmetric t)
  have hP := hSym (swapUnit (R := R) t.i t.j) (swapUnit_symmetric t.i t.j)
  have h := H.mul_mem hAP hP
  rwa [mul_assoc, swapUnit_square, mul_one] at h

def rowMatrix (i : I) (c : I → R) : Matrix I I R :=
  fun a b => if a = i then c b else 0

omit [Fintype I] in
theorem rowMatrix_add (i : I) (c d : I → R) :
    rowMatrix i (c + d) = rowMatrix i c + rowMatrix i d := by
  ext a b
  by_cases h : a = i <;> simp [rowMatrix, h]

omit [Fintype I] in
theorem rowMatrix_neg (i : I) (c : I → R) :
    rowMatrix i (-c) = -rowMatrix i c := by
  ext a b
  by_cases h : a = i <;> simp [rowMatrix, h]

theorem rowMatrix_mul (i : I) (c d : I → R) (hc : c i = 0) :
    rowMatrix i c * rowMatrix i d = 0 := by
  ext a b
  simp [Matrix.mul_apply, rowMatrix, hc]

def rowUnit (i : I) (c : I → R) (hc : c i = 0) : (Matrix I I R)ˣ where
  val := 1 + rowMatrix i c
  inv := 1 - rowMatrix i c
  val_inv := by
    rw [mul_sub, add_mul, one_mul, mul_one, add_mul, one_mul, rowMatrix_mul i c c hc]
    simp
  inv_val := by
    rw [sub_mul, mul_add, one_mul, one_mul, mul_add, mul_one, rowMatrix_mul i c c hc]
    simp

theorem rowUnit_zero (i : I) : rowUnit i (0 : I → R) (by rfl) = 1 := by
  apply Units.ext
  ext a b
  simp [rowUnit, rowMatrix]

theorem rowUnit_add (i : I) (c d : I → R) (hc : c i = 0) (hd : d i = 0) :
    rowUnit i (c + d) (by simp [hc, hd]) = rowUnit i c hc * rowUnit i d hd := by
  apply Units.ext
  change 1 + rowMatrix i (c + d) = (1 + rowMatrix i c) * (1 + rowMatrix i d)
  simp only [rowMatrix_add, mul_add, add_mul, mul_one, one_mul, rowMatrix_mul i c d hc, add_zero, add_assoc]

theorem rowUnit_single (i j : I) (hij : i ≠ j) (c : R) :
    rowUnit i (Pi.single j c) (by simp [hij]) = transvectionUnit ⟨i, j, hij, c⟩ := by
  apply Units.ext
  change 1 + rowMatrix i (Pi.single j c) = 1 + Matrix.single i j c
  congr 1
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp_all [rowMatrix, Matrix.single] <;> aesop

theorem rowUnit_mem (H : Subgroup (Matrix I I R)ˣ)
    (hSym : ∀ A : (Matrix I I R)ˣ, A.val.IsSymm → A ∈ H)
    (i : I) (c : I → R) (hc : c i = 0) : rowUnit i c hc ∈ H := by
  have hs : ∀ (s : Finset I), ∀ h : (∑ j ∈ s, Pi.single j (c j)) i = 0,
      rowUnit i (∑ j ∈ s, Pi.single j (c j)) h ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro h; simp [rowUnit_zero]
    | @insert j s hj ih =>
      intro h
      have hj0 : (Pi.single j (c j) : I → R) i = 0 := by
        by_cases he : i = j
        · subst j; simp [hc]
        · simp [he]
      have hs0 : (∑ k ∈ s, Pi.single k (c k)) i = 0 := by
        simpa [Finset.sum_insert hj, hj0] using h
      have hsingle : rowUnit i (Pi.single j (c j)) hj0 ∈ H := by
        by_cases he : i = j
        · subst j; simp [hc, rowUnit_zero]
        · rw [rowUnit_single i j he]
          exact transvection_mem H hSym _
      simpa only [← rowUnit_add i _ _ hj0 hs0, Finset.sum_insert hj] using H.mul_mem hsingle (ih hs0)
  have he : (∑ j : I, Pi.single j (c j)) = c := by
    ext k
    simp
  simpa only [he] using hs Finset.univ (by rw [he]; exact hc)

theorem rowUnit_mul_pivot (i : I) (c : I → R) (hc : c i = 0)
    (A : Matrix I I R) :
    ((rowUnit i c hc).val * A) i i = A i i + ∑ j, c j * A j i := by
  change ((1 + rowMatrix i c) * A) i i = _
  rw [Matrix.add_mul, Matrix.one_mul]
  simp [rowMatrix, Matrix.mul_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryMatrixUnits.CM
