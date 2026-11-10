module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Calculus.Quaternion.Algebra
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
public import OAI.Analysis.Calculus.Quaternion.ThirdTensor


set_option backward.privateInPublic true
@[expose] public section

/-! The algebraic principal symbol of divergence of a Hessian cofactor. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open scoped Matrix

variable {m s : Type*} [Fintype m] [Fintype s] [DecidableEq m] [DecidableEq s]

def hessianLinearMap (e : s → Q) :
    Matrix (m × s) (m × s) ℝ →ₗ[ℝ] Matrix m m Q where
  toFun := hessianMap e
  map_add' := hessianMap_add e
  map_smul' c A := hessianMap_smul e A c

def hessianSymbolComponent (e : s → Q) (D : Matrix m m Q →ₗ[ℝ] Matrix m m Q)
    (p : m × s) (b : m) : Matrix (m × s) (m × s) ℝ →ₗ[ℝ] Q where
  toFun H := star (e p.2) * D (hessianMap e H) p.1 b
  map_add' H K := by simp [hessianMap_add, map_add, mul_add]
  map_smul' c H := by simp [hessianMap_smul, map_smul]

omit [DecidableEq m] [DecidableEq s] in
theorem hessianSymbol_rankOne (e : s → Q) (D : Matrix m m Q →ₗ[ℝ] Matrix m m Q)
    (ξ : m × s → ℝ) (b : m) :
    (∑ p, ξ p • hessianSymbolComponent e D p b (fun q r => ξ q * ξ r)) =
      (star (gradientMap e ξ) ᵥ* D (outer (gradientMap e ξ))) b := by
  simp only [hessianSymbolComponent, LinearMap.coe_mk, AddHom.coe_mk,
    hessianMap_rankOne, Fintype.sum_prod_type, Matrix.vecMul, dotProduct,
    Pi.star_apply, gradientMap, star_sum, Quaternion.star_smul, Finset.sum_mul,
    smul_mul_assoc]

/-- The exact algebraic cancellation used for the divergence of a Hessian cofactor.
The hypothesis is only a property of its linearized matrix map; all differential
information is contained in the symmetric third tensor `T`. -/
theorem hessian_cofactor_symbol_zero (e : s → Q)
    (D : Matrix m m Q →ₗ[ℝ] Matrix m m Q)
    (hD : ∀ g : m → Q, star g ᵥ* D (outer g) = 0)
    (T : (m × s) → (m × s) → (m × s) → ℝ)
    (h12 : ∀ p q r, T p q r = T q p r)
    (h23 : ∀ p q r, T p q r = T p r q) (b : m) :
    strongDivergence e (fun p => D (hessianMap e (T p))) b = 0 := by
  have hL (ξ : m × s → ℝ) :
      ∑ p, ξ p • hessianSymbolComponent e D p b (fun q r => ξ q * ξ r) = 0 := by
    rw [hessianSymbol_rankOne, hD]
    rfl
  have h := symmetric_third_tensor_cancellation
    (fun p => hessianSymbolComponent e D p b) hL T h12 h23
  simpa only [strongDivergence, Fintype.sum_prod_type, hessianSymbolComponent,
    LinearMap.coe_mk, AddHom.coe_mk] using h

end OAI.Analysis.Calculus.Quaternion
