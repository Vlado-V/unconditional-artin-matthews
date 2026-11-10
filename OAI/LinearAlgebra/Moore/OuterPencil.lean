module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import OAI.Analysis.Calculus.Quaternion.Algebra
public import OAI.LinearAlgebra.Moore.Derivative
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Energy.Algebra
public import OAI.LinearAlgebra.Moore.Boundary
public import OAI.LinearAlgebra.Moore.Cofactor
public import OAI.LinearAlgebra.Moore.Outer
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The arbitrary-rank-one determinant segment and its exact energy integral. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion
open scoped MatrixOrder ComplexOrder

theorem mooreDet_outer_zero (n : ℕ) (v : Fin (n + 2) → Quaternion ℝ) :
    mooreDet (n + 2) (OAI.Analysis.Calculus.Quaternion.outer v) = 0 := by
  rw [← columnExtension_projector v (0 : Fin (n + 2)), mooreDet_congruence,
    mooreDet_coordinateProjector_zero, mul_zero]

theorem mooreDet_outer_pencil (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (v : Fin (n + 2) → Quaternion ℝ) (t s : ℝ) :
    mooreDet (n + 2) (t • A + s • OAI.Analysis.Calculus.Quaternion.outer v) =
      t ^ (n + 2) * mooreDet (n + 2) A +
      s * t ^ (n + 1) * mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) := by
  by_cases ht : t = 0
  · simp [ht, mooreDet_smul, mooreDet_outer_zero]
  · have hm : t • A + s • OAI.Analysis.Calculus.Quaternion.outer v = t • (A + (s / t) • OAI.Analysis.Calculus.Quaternion.outer v) := by
      rw [smul_add, smul_smul]
      congr 1
      rw [mul_div_cancel₀ s ht]
    rw [hm, mooreDet_smul, mooreDet_add_outer_differential]
    have hpow : t ^ (n + 2) = t ^ (n + 1) * t := pow_succ t (n + 1)
    rw [hpow]
    field_simp

theorem mooreDet_outer_segment (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (v : Fin (n + 2) → Quaternion ℝ) (t : ℝ) :
    mooreDet (n + 2) (t • A + (1 - t) • OAI.Analysis.Calculus.Quaternion.outer v) =
      t ^ (n + 2) * mooreDet (n + 2) A +
      (1 - t) * t ^ (n + 1) * mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) :=
  mooreDet_outer_pencil n A v t (1 - t)

theorem integral_mooreDet_outer_segment (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (v : Fin (n + 2) → Quaternion ℝ) :
    (∫ t in (0 : ℝ)..1, mooreDet (n + 2) (t • A + (1 - t) • OAI.Analysis.Calculus.Quaternion.outer v)) =
      mooreDet (n + 2) A / ((n : ℝ) + 3) +
      mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have hf : (fun t : ℝ ↦ mooreDet (n + 2) (t • A + (1 - t) • OAI.Analysis.Calculus.Quaternion.outer v)) =
      fun t ↦ t ^ ((n + 1) + 1) * mooreDet (n + 2) A +
        t ^ (n + 1) * (1 - t) * mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) := by
    funext t
    rw [mooreDet_outer_segment]
    ring
  rw [hf, OAI.Analysis.PDE.Energy.integral_segment]
  norm_num [Nat.cast_add, Nat.cast_one]
  congr 2 <;> ring

theorem mooreDifferential_outer_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ)
    (hA : (complexify A).PosSemidef) : 0 ≤ mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer v) :=
  mooreDifferential_nonneg_of_posSemidef A (OAI.Analysis.Calculus.Quaternion.outer v) hA (complexify_outer_posSemidef v)

end OAI.LinearAlgebra.Moore
