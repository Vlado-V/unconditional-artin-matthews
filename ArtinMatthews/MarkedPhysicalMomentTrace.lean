module

public import ArtinMatthews.MarkedPhysicalLocalizedMoment
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


set_option backward.privateInPublic true
@[expose] public section

/-! The physical moment is exactly the original constant-mass trace on
vectors one on every list at one position. No list normalization occurs. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical ComplexOrder
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

theorem markedPSD_quadratic_real_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (r : ℝ) (f : ι → ℂ) :
    markedQuadraticForm B ((r:ℂ) • f)=r^2*markedQuadraticForm B f := by
  simp_rw [markedQuadraticForm_spectral B hB.isHermitian,Matrix.mulVec_smul,
    Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def markedPhysicalUnnormalizedPositionVector {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (z : Z) :
    MarkedPhysicalState P M Z → ℂ := fun s => if s.1.1=z then 1 else 0

theorem markedPhysicalPositionMoment_eq_original_mass
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (V : J → ℝ) (hV : ∀ j,0≤V j)
    (A : Matrix (MarkedPhysicalState P M Z) (MarkedPhysicalState P M Z) ℂ) (r : ℕ) :
    markedPhysicalPositionMoment P M Z V A r =
      markedPhysicalMass V M * ∑ z : Z, markedQuadraticForm ((A*Aᴴ)^r)
        (markedPhysicalUnnormalizedPositionVector P M Z z) := by
  unfold markedPhysicalPositionMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have he : markedPositionVector
      (fun s : MarkedPhysicalState P M Z => s.1.1) (markedPhysicalMass V M) z =
      (Real.sqrt (markedPhysicalMass V M):ℂ) • markedPhysicalUnnormalizedPositionVector P M Z z := by
    funext s
    by_cases hs : s.1.1=z <;>
      simp [markedPositionVector,markedPhysicalUnnormalizedPositionVector,hs]
  rw [he,markedPSD_quadratic_real_scale _ ((Matrix.posSemidef_self_mul_conjTranspose A).pow r),
    Real.sq_sqrt (markedPhysicalMass_nonneg V M hV)]

end
end ArtinMatthews
