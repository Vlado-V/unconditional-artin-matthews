module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import OAI.LinearAlgebra.Moore.Derivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.LinearAlgebra.Moore.Elliptic
public import OAI.LinearAlgebra.Moore.Inverse
public import OAI.LinearAlgebra.Moore.Positive
public import OAI.LinearAlgebra.Moore.PositiveInverse


set_option backward.privateInPublic true
@[expose] public section

/-! Strict ellipticity and determinant monotonicity on the positive cone. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix Set
open scoped MatrixOrder ComplexOrder

theorem complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n (Quaternion ℝ)) = 0 := by
  apply Matrix.ext
  intro ⟨i, a⟩ ⟨j, b⟩
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M a b) quaternionMatrix_zero

theorem complex_congruence_diag {ι : Type*} [Fintype ι]
    (A C : Matrix ι ι ℂ) (i : ι) :
    (C * A * Cᴴ) i i =
      star (fun j ↦ star (C i j)) ⬝ᵥ A *ᵥ (fun j ↦ star (C i j)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_star, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- A positive definite matrix has strictly positive trace pairing with every
nonzero positive semidefinite matrix. -/
theorem complex_trace_mul_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosSemidef) (hB0 : B ≠ 0) :
    0 < (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [star_eq_conjTranspose] at hB0 ⊢
  have hC0 : C ≠ 0 := by
    intro h
    apply hB0
    simp [h]
  obtain ⟨i, j, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hC0 (Matrix.ext h)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hP := hA.posSemidef.mul_mul_conjTranspose_same C
  have heq : (C * A * Cᴴ).trace.re = ∑ k, ((C * A * Cᴴ) k k).re := by
    simp [Matrix.trace]
  rw [heq]
  apply Finset.sum_pos'
  · intro k _
    exact (Complex.nonneg_iff.mp (hP.diag_nonneg (i := k))).1
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [complex_congruence_diag]
    apply (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos ?_)).1
    intro h
    have he := congrFun h j
    simp only [Pi.zero_apply, star_eq_zero] at he
    exact hij he

theorem mooreDifferential_nonneg_of_posDef {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify D).PosSemidef) :
    0 ≤ mooreDifferential n A D := by
  obtain ⟨C, hAC, hCA⟩ := exists_quaternion_inverse_of_complexify_posDef A hA
  exact mooreDifferential_nonneg n A D C hA hD hAC hCA
    (mooreDet_pos_of_complexify_posDef A hA).le

theorem mooreDifferential_pos_of_posDef {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify D).PosSemidef) (hD0 : D ≠ 0) :
    0 < mooreDifferential n A D := by
  rw [mooreDifferential_eq_complex_inverse A D hA (isHermitian_of_complexify hD.isHermitian)]
  apply mul_pos (mooreDet_pos_of_complexify_posDef A hA)
  apply div_pos _ (by norm_num)
  apply complex_trace_mul_pos hA.inv hD
  intro he
  apply hD0
  apply complexify_injective
  exact he.trans complexify_zero.symm

theorem hasDerivAt_mooreDet_affine {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ) :
    HasDerivAt (fun s ↦ mooreDet n (A + s • D)) (mooreDifferential n (A + t • D) D) t := by
  apply hasDerivAt_mooreDet_path
  intro i j
  convert! (hasDerivAt_const t (A i j)).add ((hasDerivAt_id t).smul_const (D i j)) using 1
  simp

/-- Monotonicity in every positive semidefinite direction, with no extra
determinant sign or inverse assumptions. -/
theorem mooreDet_le_of_posSemidef_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify (B - A)).PosSemidef) :
    mooreDet n A ≤ mooreDet n B := by
  let D := B - A
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (complexify (A + t • D)).PosDef := by
    rw [complexify_add, complexify_real_smul]
    exact hA.add_posSemidef (hD.smul ht.1)
  have hcont : ContinuousOn (fun t ↦ mooreDet n (A + t • D)) (Icc (0 : ℝ) 1) :=
    fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1) hcont
    (fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).hasDerivWithinAt)
    (fun t ht ↦ mooreDifferential_nonneg_of_posDef _ _ (hpos t (interior_subset ht)) hD)
  simpa [D] using hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_le_one

/-- Strict determinant increase for every nonzero positive semidefinite direction. -/
theorem mooreDet_lt_of_posSemidef_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify (B - A)).PosSemidef) (hBA : B ≠ A) :
    mooreDet n A < mooreDet n B := by
  let D := B - A
  have hD0 : D ≠ 0 := sub_ne_zero.mpr hBA
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (complexify (A + t • D)).PosDef := by
    rw [complexify_add, complexify_real_smul]
    exact hA.add_posSemidef (hD.smul ht.1)
  have hcont : ContinuousOn (fun t ↦ mooreDet n (A + t • D)) (Icc (0 : ℝ) 1) :=
    fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).continuousAt.continuousWithinAt
  have hm := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) 1) hcont
    (fun t _ ↦ (hasDerivAt_mooreDet_affine A D t).hasDerivWithinAt)
    (fun t ht ↦ mooreDifferential_pos_of_posDef _ _ (hpos t (interior_subset ht)) hD hD0)
  simpa [D] using hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_lt_one

end OAI.LinearAlgebra.Moore
