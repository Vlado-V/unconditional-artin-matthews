module

public import ArtinMatthews.VaryingKummerAnalyticGaussian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Analysis.Matrix.Normed


set_option backward.privateInPublic true
@[expose] public section

/-! Generic periodic-lattice proof extraction from OpenAI PrimePackets/IdealClasses.lean.
Only namespace/import routing changes; no number-field signature assumptions. -/
namespace ArtinMatthews.ReusedTheta
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open WithLp Asymptotics

variable {d : Type*} [Fintype d]

 
def cosetLatticeTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) : ℂ :=
  ∑' z : d → ℤ, Complex.exp (-(b:ℂ) *
    ‖B (toLp 2 x + euclideanInteger z)‖^2)

lemma cosetLatticeTheta_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => Complex.exp (-(b:ℂ) *
      ‖B (toLp 2 x + euclideanInteger z)‖^2)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm
    (coordinateGaussian_locallyNormal (coordinateBasis B) b hb)
  have H' := (ContinuousMap.evalCLM ℂ (x := x)).summable H
  simpa [translate, coordinateGaussian, coordinateBasis, euclideanInteger, toLp_add] using H'

lemma cosetPhase_norm (m : d → ℤ) (x : d → ℝ) :
    ‖UnitAddTorus.mFourier m (torusProjection x)‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma twistedDualGaussian_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    Summable (fun m : d → ℤ => Complex.exp (-(b:ℂ) *
      ‖B (euclideanInteger m)‖^2) * UnitAddTorus.mFourier m (torusProjection x)) := by
  apply Summable.of_norm_bounded (latticeTheta_summable B b hb).norm
  intro m
  simp [cosetPhase_norm]

 

theorem cosetLatticeTheta_poisson
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    cosetLatticeTheta B x b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ∑' m : d → ℤ, Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) *
          UnitAddTorus.mFourier m (torusProjection x) := by
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hsum : Summable (fun m : d → ℤ =>
      ∫ y, fourierCharacter m y * coordinateGaussian (coordinateBasis B) b y) := by
    simp_rw [coordinateGaussian_fourier B b hb]
    exact (latticeTheta_summable (adjointEquiv B.symm) _ hb').mul_left _
  have H := multivariate_poisson (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb) (coordinateGaussian_integrable B b hb) hsum x
  simp only [coordinateGaussian_fourier B b hb, mul_assoc, tsum_mul_left] at H
  simpa [cosetLatticeTheta, coordinateGaussian, coordinateBasis, euclideanInteger, toLp_add,
    mul_assoc] using H

 

def congruenceTheta {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) : ℂ :=
  ∑ i, w i * cosetLatticeTheta B (x i) b

 
def congruenceThetaFourierWeight {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) (m : d → ℤ) : ℂ :=
  ∑ i, w i * UnitAddTorus.mFourier m (torusProjection (x i))

@[simp] lemma congruenceThetaFourierWeight_zero {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) :
    congruenceThetaFourierWeight x w 0 = ∑ i, w i := by
  simp [congruenceThetaFourierWeight, UnitAddTorus.mFourier]

 

theorem congruenceTheta_poisson {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) (hb : 0 < b) :
    congruenceTheta B x w b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ∑' m : d → ℤ, Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) *
          congruenceThetaFourierWeight x w m := by
  classical
  let A : ℂ := ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
    (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2)
  let F (m : d → ℤ) := Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
    ‖adjointEquiv B.symm (euclideanInteger m)‖^2)
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hs (i : I) : Summable (fun m : d → ℤ =>
      w i * (F m * UnitAddTorus.mFourier m (torusProjection (x i)))) :=
    (twistedDualGaussian_summable (adjointEquiv B.symm) (x i) _ hb').mul_left _
  unfold congruenceTheta
  simp_rw [cosetLatticeTheta_poisson B _ b hb]
  change (∑ i, w i * (A * ∑' m, F m *
    UnitAddTorus.mFourier m (torusProjection (x i)))) = _
  calc
    _ = A * ∑ i, ∑' m, w i * (F m *
        UnitAddTorus.mFourier m (torusProjection (x i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [tsum_mul_left]
      ring
    _ = A * ∑' m, ∑ i, w i * (F m *
        UnitAddTorus.mFourier m (torusProjection (x i))) := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro m
      simp only [congruenceThetaFourierWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring


end
end ArtinMatthews.ReusedTheta
