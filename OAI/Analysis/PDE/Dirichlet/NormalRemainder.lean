module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

open scoped InnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def realTangentProjection (ν v : E) : E := v - ⟪ν, v⟫_ℝ • ν

theorem realTangentProjection_tangent {ν : E} (hν : ‖ν‖ = 1) (v : E) :
    ⟪ν, realTangentProjection ν v⟫_ℝ = 0 := by
  simp [realTangentProjection, inner_sub_right, real_inner_smul_right,
    hν]

theorem realTangentProjection_norm {ν v : E} (hν : ‖ν‖ = 1) (hv : ‖v‖ ≤ 1) :
    ‖realTangentProjection ν v‖ ≤ 2 := by
  have hi : |⟪ν, v⟫_ℝ| ≤ 1 := (abs_real_inner_le_norm ν v).trans (by simpa [hν] using hv)
  calc
    _ ≤ ‖v‖ + ‖⟪ν, v⟫_ℝ • ν‖ := norm_sub_le _ _
    _ = ‖v‖ + |⟪ν, v⟫_ℝ| := by rw [norm_smul, Real.norm_eq_abs, hν, mul_one]
    _ ≤ 2 := by linarith

/-- Once tangential and mixed entries are controlled, subtracting the
single unknown normal-normal entry leaves a bounded bilinear form. -/
theorem normal_remainder_abs_bound (H : E →L[ℝ] E →L[ℝ] ℝ) {ν v w : E}
    (hν : ‖ν‖ = 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hH : ∀ x y, H x y = H y x) {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (ht : ∀ x y, ⟪ν, x⟫_ℝ = 0 → ⟪ν, y⟫_ℝ = 0 → |H x y| ≤ T * ‖x‖ * ‖y‖)
    (hm : ∀ x, ⟪ν, x⟫_ℝ = 0 → |H ν x| ≤ M * ‖x‖) :
    |H v w - H ν ν * ⟪ν, v⟫_ℝ * ⟪ν, w⟫_ℝ| ≤ 4 * T + 4 * M := by
  let x := realTangentProjection ν v
  let y := realTangentProjection ν w
  have hx : ‖x‖ ≤ 2 := realTangentProjection_norm hν hv
  have hy : ‖y‖ ≤ 2 := realTangentProjection_norm hν hw
  have hx0 : ⟪ν, x⟫_ℝ = 0 := realTangentProjection_tangent hν v
  have hy0 : ⟪ν, y⟫_ℝ = 0 := realTangentProjection_tangent hν w
  have hav : |⟪ν, v⟫_ℝ| ≤ 1 := (abs_real_inner_le_norm ν v).trans (by simpa [hν] using hv)
  have haw : |⟪ν, w⟫_ℝ| ≤ 1 := (abs_real_inner_le_norm ν w).trans (by simpa [hν] using hw)
  have hxy : |H x y| ≤ 4 * T := by
    have hprod : ‖x‖ * ‖y‖ ≤ 4 := by
      calc
        _ ≤ 2 * 2 := mul_le_mul hx hy (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    calc
      _ ≤ T * ‖x‖ * ‖y‖ := ht x y hx0 hy0
      _ = T * (‖x‖ * ‖y‖) := mul_assoc _ _ _
      _ ≤ T * 4 := mul_le_mul_of_nonneg_left hprod hT
      _ = 4 * T := mul_comm _ _
  have hmx : |H ν x| ≤ 2 * M := (hm x hx0).trans (by nlinarith)
  have hmy : |H ν y| ≤ 2 * M := (hm y hy0).trans (by nlinarith)
  have hxterm : |⟪ν, w⟫_ℝ * H ν x| ≤ 2 * M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right haw (abs_nonneg _)).trans (by simpa using hmx)
  have hyterm : |⟪ν, v⟫_ℝ * H ν y| ≤ 2 * M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hav (abs_nonneg _)).trans (by simpa using hmy)
  have heq : H v w - H ν ν * ⟪ν, v⟫_ℝ * ⟪ν, w⟫_ℝ =
      H x y + ⟪ν, v⟫_ℝ * H ν y + ⟪ν, w⟫_ℝ * H ν x := by
    simp only [x, y, realTangentProjection, map_sub, map_smul, sub_apply, smul_apply,
      smul_eq_mul]
    rw [hH v ν]
    ring
  rw [heq]
  calc
    _ ≤ |H x y + ⟪ν, v⟫_ℝ * H ν y| + |⟪ν, w⟫_ℝ * H ν x| := abs_add_le _ _
    _ ≤ (|H x y| + |⟪ν, v⟫_ℝ * H ν y|) + |⟪ν, w⟫_ℝ * H ν x| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 4 * T + 4 * M := by linarith

end Inner
end OAI.Analysis.PDE.Dirichlet
