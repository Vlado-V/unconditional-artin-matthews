module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.LinearAlgebra.Moore.Basic
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

/-! Singularity of the signed Moore determinant from a quaternionic null vector. -/

namespace OAI.LinearAlgebra.Moore

open Matrix

/-- A normalized null vector yields a singular congruence projection fixing
the Hermitian matrix, so its Moore determinant vanishes. -/
theorem mooreDet_zero_of_normalized_kernel (n : ℕ)
    (H : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hH : H.IsHermitian)
    (v : Fin n → Quaternion ℝ) (k : Fin n) (hvk : v k = 1)
    (hv : H *ᵥ v = 0) : mooreDet n H = 0 := by
  let e : Fin n → Quaternion ℝ := Pi.single k 1
  let R : Matrix (Fin n) (Fin n) (Quaternion ℝ) := 1 - vecMulVec v e
  have hHeq : Hᴴ = H := hH
  have hright : H * R = H := by
    dsimp only [R]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_vecMulVec, hv]
    simp
  have hleft : Rᴴ * H = H := by
    simpa only [Matrix.conjTranspose_mul, hHeq] using congrArg Matrix.conjTranspose hright
  have hcong : Rᴴ * H * (Rᴴ)ᴴ = H := by
    rw [Matrix.conjTranspose_conjTranspose, hleft, hright]
  have hdet : (complexify R).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (k, 0)
    rintro ⟨j, b⟩
    have hrow : R k j = 0 := by
      simp [R, e, Matrix.one_apply, vecMulVec_apply, hvk, Pi.single_apply, eq_comm]
    change quaternionMatrix (R k j) 0 b = 0
    rw [hrow, quaternionMatrix_zero]
    rfl
  have h := mooreDet_congruence n H Rᴴ
  rw [hcong, complexify_star, Matrix.det_conjTranspose, hdet] at h
  simpa using h

/-- A nonzero right-null vector forces the signed Moore determinant of a
Hermitian quaternionic matrix to vanish, in every finite dimension. -/
theorem mooreDet_zero_of_kernel (n : ℕ)
    (H : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hH : H.IsHermitian)
    (v : Fin n → Quaternion ℝ) (hv : H *ᵥ v = 0) (hne : v ≠ 0) :
    mooreDet n H = 0 := by
  have hex : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hex
  let w : Fin n → Quaternion ℝ := fun j => v j * (v k)⁻¹
  have hwk : w k = 1 := mul_inv_cancel₀ hk
  have hw : H *ᵥ w = 0 := by
    funext j
    change (∑ i, H j i * (v i * (v k)⁻¹)) = 0
    simp only [← mul_assoc, ← Finset.sum_mul]
    change (H *ᵥ v) j * (v k)⁻¹ = 0
    rw [hv]
    simp
  exact mooreDet_zero_of_normalized_kernel n H hH w k hwk hw

end OAI.LinearAlgebra.Moore
