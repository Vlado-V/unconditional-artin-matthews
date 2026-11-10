module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Dirichlet.Hessian
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

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix MatrixOrder

/-- The quaternion-valued quadratic form, with multiplication order fixed. -/
def quaternionForm {m : ℕ} (A : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (z : Fin m → Quaternion ℝ) : Quaternion ℝ :=
  ∑ i, ∑ j, star (z i) * A i j * z j

theorem quaternionForm_add {m : ℕ} (A B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (z : Fin m → Quaternion ℝ) : quaternionForm (A + B) z =
      quaternionForm A z + quaternionForm B z := by
  simp [quaternionForm, mul_add, add_mul, Finset.sum_add_distrib]

theorem quaternionForm_sum {m : ℕ} {ι : Type*} (t : Finset ι)
    (A : ι → Matrix (Fin m) (Fin m) (Quaternion ℝ)) (z : Fin m → Quaternion ℝ) :
    quaternionForm (∑ k ∈ t, A k) z = ∑ k ∈ t, quaternionForm (A k) z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [quaternionForm]
  | @insert k t hk ih => simp [hk, quaternionForm_add, ih]

theorem hessianMap_sum {m s : ℕ} {ι : Type*} (t : Finset ι)
    (e : Fin s → Quaternion ℝ) (A : ι → Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ) :
    OAI.Analysis.Calculus.Quaternion.hessianMap e (∑ k ∈ t, A k) = ∑ k ∈ t, OAI.Analysis.Calculus.Quaternion.hessianMap e (A k) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply Matrix.ext
    intro i j
    simp [OAI.Analysis.Calculus.Quaternion.hessianMap]
  | @insert k t hk ih => simp [hk, OAI.Analysis.Calculus.Quaternion.hessianMap_add, ih]

theorem quaternionForm_outer_nonneg {m : ℕ} (g z : Fin m → Quaternion ℝ) :
    0 ≤ (quaternionForm (OAI.Analysis.Calculus.Quaternion.outer g) z).re := by
  simpa only [quaternionForm, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    using OAI.Analysis.Calculus.Quaternion.outer_quadratic_nonneg g z

/-- The quaternionic Hessian map preserves positivity of a real Hessian. -/
theorem hessianMap_nonneg {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {H : Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ} (hH : H.PosSemidef)
    (z : Fin m → Quaternion ℝ) : 0 ≤ (quaternionForm (OAI.Analysis.Calculus.Quaternion.hessianMap e H) z).re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose]
  have hC : Cᴴ * C = ∑ k, Matrix.of (fun i j ↦ C k i * C k j) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.sum_apply]
  rw [hC, hessianMap_sum]
  have hrow (k : Fin m × Fin s) :
      OAI.Analysis.Calculus.Quaternion.hessianMap e (Matrix.of (fun i j ↦ C k i * C k j)) =
        OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i)) := OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne e (fun i ↦ C k i)
  simp_rw [hrow]
  rw [quaternionForm_sum]
  have hre : (∑ k, quaternionForm (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i))) z).re =
      ∑ k, (quaternionForm (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i))) z).re := by
    let F : Fin m × Fin s → Quaternion ℝ := fun k ↦
      quaternionForm (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i))) z
    change (∑ k, F k).re = ∑ k, (F k).re
    generalize (Finset.univ : Finset (Fin m × Fin s)) = t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert k t hk ih => simp [hk, ih]
  rw [hre]
  exact Finset.sum_nonneg fun k _ ↦ quaternionForm_outer_nonneg _ _

theorem quaternionHessian_nonpos_of_localMax {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace m s → ℝ} {x : CoordinateSpace m s}
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) (z : Fin m → Quaternion ℝ) :
    (quaternionForm (quaternionHessian e f x) z).re ≤ 0 := by
  have h := hessianMap_nonneg e (realHessian_neg_posSemidef_of_localMax hf hmax) z
  have hn : OAI.Analysis.Calculus.Quaternion.hessianMap e (-realHessian f x) = -quaternionHessian e f x := by
    apply Matrix.ext
    intro i j
    simp [OAI.Analysis.Calculus.Quaternion.hessianMap, quaternionHessian, Finset.sum_neg_distrib]
  rw [hn] at h
  simpa [quaternionForm, mul_neg, neg_mul, Finset.sum_neg_distrib] using h

theorem hessianMap_one {m s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α, e α * star (e α) = 1) :
    OAI.Analysis.Calculus.Quaternion.hessianMap (m := Fin m) e (1 : Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ) =
      s • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [OAI.Analysis.Calculus.Quaternion.hessianMap, Matrix.one_apply, he]
  · simp [OAI.Analysis.Calculus.Quaternion.hessianMap, hij]

/-- The exact quadratic barrier Hessian used in the four-slot Dirichlet estimates. -/
theorem quaternionHessian_four_norm_sq {m : ℕ} (x : CoordinateSpace m 4) :
    quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y : CoordinateSpace m 4 ↦ ‖y‖ ^ 2) x =
      (8 : ℝ) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  have he (α : Fin 4) : OAI.Analysis.Calculus.Quaternion.fourSlots α * star (OAI.Analysis.Calculus.Quaternion.fourSlots α) = 1 := by
    fin_cases α <;> ext <;> norm_num [OAI.Analysis.Calculus.Quaternion.fourSlots, Quaternion.re_mul]
  unfold quaternionHessian
  rw [realHessian_norm_sq, OAI.Analysis.Calculus.Quaternion.hessianMap_smul, hessianMap_one OAI.Analysis.Calculus.Quaternion.fourSlots he]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

end OAI.Analysis.PDE.Dirichlet
