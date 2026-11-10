module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Dirichlet.Quaternion
public import OAI.LinearAlgebra.Moore.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.LinearAlgebra.Moore.Elliptic
public import OAI.LinearAlgebra.Moore.Form


set_option backward.privateInPublic true
@[expose] public section

/-! A positive quaternionic matrix has a genuine two-sided quaternionic inverse. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.PDE.Dirichlet
open scoped MatrixOrder ComplexOrder

def quaternionMulVecLinear {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    (Fin n → Quaternion ℝ) →ₗ[ℝ] (Fin n → Quaternion ℝ) where
  toFun := A.mulVec
  map_add' := A.mulVec_add
  map_smul' := by
    intro c z
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum]

theorem quaternionForm_eq_dotProduct {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (z : Fin n → Quaternion ℝ) :
    OAI.Analysis.PDE.Dirichlet.quaternionForm A z = star z ⬝ᵥ A *ᵥ z := by
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    mul_assoc]

theorem quaternionMulVec_injective_of_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hpos : ∀ z ≠ 0, 0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re) : Function.Injective A.mulVec := by
  change Function.Injective (quaternionMulVecLinear A)
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  by_contra hne
  have hp := hpos z hne
  have hz' : A *ᵥ z = 0 := hz
  rw [quaternionForm_eq_dotProduct, hz'] at hp
  simp at hp

/-- The inverse is constructed from surjectivity of real-linear multiplication;
no commutative determinant or quaternionic spectral theorem is assumed. -/
theorem exists_quaternion_inverse_of_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hpos : ∀ z ≠ 0, 0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re) :
    ∃ C : Matrix (Fin n) (Fin n) (Quaternion ℝ), A * C = 1 ∧ C * A = 1 := by
  have hi := quaternionMulVec_injective_of_pos A hpos
  have hs : Function.Surjective (quaternionMulVecLinear A) :=
    LinearMap.surjective_of_injective hi
  choose v hv using hs
  let C : Matrix (Fin n) (Fin n) (Quaternion ℝ) := fun i j ↦ v (Pi.single j 1) i
  have hAC : A * C = 1 := by
    apply Matrix.ext
    intro i j
    have h := congrFun (hv (Pi.single j 1)) i
    change (A *ᵥ v (Pi.single j 1)) i = (Pi.single j (1 : Quaternion ℝ) : Fin n → Quaternion ℝ) i at h
    change (A *ᵥ v (Pi.single j 1)) i = (1 : Matrix _ _ _) i j
    simpa only [Matrix.one_apply, Pi.single_apply, eq_comm] using h
  refine ⟨C, hAC, ?_⟩
  have he : A * (C * A) = A * 1 := by rw [← Matrix.mul_assoc, hAC, one_mul, mul_one]
  apply Matrix.ext
  intro i j
  apply congrFun (hi (a₁ := fun k ↦ (C * A) k j) (a₂ := fun k ↦ (1 : Matrix _ _ _) k j) ?_) i
  funext k
  exact congrFun (congrFun he k) j

theorem exists_quaternion_inverse_of_complexify_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (complexify A).PosDef) :
    ∃ C : Matrix (Fin n) (Fin n) (Quaternion ℝ), A * C = 1 ∧ C * A = 1 :=
  exists_quaternion_inverse_of_pos A
    ((complexify_posDef_iff (isHermitian_of_complexify hA.isHermitian)).mp hA)

end OAI.LinearAlgebra.Moore
