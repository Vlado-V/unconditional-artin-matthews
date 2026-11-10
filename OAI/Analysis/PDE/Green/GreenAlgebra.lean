module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.LinearAlgebra.Moore.Cofactor
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Real coefficient contractions for the quaternionic Green identities. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem quaternion_re_triple_cycle (p q r : Quaternion ℝ) :
    (p * (q * r)).re = (r * p * q).re := by
  rw [← mul_assoc, OAI.LinearAlgebra.Moore.quaternion_re_mul_comm]
  rw [mul_assoc]

theorem realTrace_hessianMap_transpose {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (e : Fin s → Quaternion ℝ)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) :
    OAI.LinearAlgebra.Moore.realTrace (A * OAI.Analysis.Calculus.Quaternion.hessianMap e H) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e A p q * H q p := by
  simp only [OAI.LinearAlgebra.Moore.realTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply, OAI.Analysis.Calculus.Quaternion.hessianMap,
    Finset.mul_sum, mul_smul_comm, OAI.LinearAlgebra.Moore.quaternion_re_sum, Quaternion.re_smul,
    OAI.Analysis.Calculus.Quaternion.realCoefficients, Fintype.sum_prod_type, quaternion_re_triple_cycle]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, ∑ α, ∑ β, H (j, α) (i, β) * (star (e β) * A i j * e α).re) =
        ∑ j, ∑ β, ∑ α, H (j, α) (i, β) * (star (e β) * A i j * e α).re := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ β, ∑ j, ∑ α, H (j, α) (i, β) * (star (e β) * A i j * e α).re :=
      Finset.sum_comm
    _ = _ := by simp_rw [mul_comm]

theorem realTrace_hessianMap {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (e : Fin s → Quaternion ℝ)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) (hH : H.IsSymm) :
    OAI.LinearAlgebra.Moore.realTrace (A * OAI.Analysis.Calculus.Quaternion.hessianMap e H) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e A p q * H p q := by
  rw [realTrace_hessianMap_transpose]
  have he (p q : Fin n × Fin s) : H q p = H p q := congrFun (congrFun hH p) q
  simp_rw [he]

theorem realCoefficients_quadratic {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (e : Fin s → Quaternion ℝ)
    (ξ : Fin n × Fin s → ℝ) :
    (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e A p q * (ξ p * ξ q)) =
      (OAI.Analysis.PDE.Dirichlet.quaternionForm A (OAI.Analysis.Calculus.Quaternion.gradientMap e ξ)).re := by
  let H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ := fun p q ↦ ξ p * ξ q
  have hH : H.IsSymm := by
    apply Matrix.ext
    intro p q
    exact mul_comm _ _
  have he := realTrace_hessianMap A e H hH
  rw [show OAI.Analysis.Calculus.Quaternion.hessianMap e H = OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e ξ) from OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne e ξ,
    OAI.LinearAlgebra.Moore.realTrace_mul_outer] at he
  exact he.symm

def realCoefficientLinear {n s : ℕ} (e : Fin s → Quaternion ℝ) (p q : Fin n × Fin s) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →ₗ[ℝ] ℝ where
  toFun := fun A ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients e A p q
  map_add' A B := by simp [OAI.Analysis.Calculus.Quaternion.realCoefficients, mul_add, add_mul]
  map_smul' c A := by simp [OAI.Analysis.Calculus.Quaternion.realCoefficients]

def realCoefficientCLM {n s : ℕ} (e : Fin s → Quaternion ℝ) (p q : Fin n × Fin s) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] ℝ :=
  (realCoefficientLinear e p q).toContinuousLinearMap

end OAI.Analysis.PDE.Green
