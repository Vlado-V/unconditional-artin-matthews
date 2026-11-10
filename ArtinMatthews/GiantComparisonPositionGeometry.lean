module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
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


set_option backward.privateInPublic true
@[expose] public section

/-! The two physical positions in a product cell stay in one fixed
positive normalized interval. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem giantComparisonProductCell_bounds {U V u v : ℕ}
    (hu : u ∈ Ico U (U+4*U)) (hv : v ∈ Ico V (V+4*V)) :
    U*V ≤ u*v ∧ u*v ≤ 25*(U*V) := by
  obtain ⟨hu₁,hu₂⟩ := mem_Ico.mp hu
  obtain ⟨hv₁,hv₂⟩ := mem_Ico.mp hv
  refine ⟨Nat.mul_le_mul hu₁ hv₁, ?_⟩
  calc
    _ ≤ (U+4*U)*(V+4*V) := Nat.mul_le_mul hu₂.le hv₂.le
    _ = _ := by ring

theorem giantComparisonPositionCell_geometry {a b x W : ℝ} {w d : ℕ}
    (ha : 0 < a) (hx : 1 ≤ x) (hW : 0 < W) (hd : W ≤ (d:ℝ))
    (hd' : (d:ℝ) ≤ 25*W) (hw : (w:ℝ)/(x*(d:ℝ)) ∈ Set.Icc a b) :
    0 < w ∧ (w:ℝ)/(x*W) ∈ Set.Icc a (25*(b+1)) ∧
      ((w+d:ℕ):ℝ)/(x*W) ∈ Set.Icc a (25*(b+1)) := by
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hD : 0 < (d:ℝ) := hW.trans_le hd
  have hB : 0 < b := ha.trans_le (hw.1.trans hw.2)
  have hxd : 0 < x*(d:ℝ) := mul_pos hx' hD
  have hlo : a*(x*W) ≤ (w:ℝ) :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hx'.le) ha.le).trans
      ((le_div_iff₀ hxd).mp hw.1)
  have hhi : (w:ℝ) ≤ 25*b*(x*W) := by
    calc
      _ ≤ b*(x*(d:ℝ)) := (div_le_iff₀ hxd).mp hw.2
      _ ≤ b*(x*(25*W)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd' hx'.le) hB.le
      _ = _ := by ring
  have hXY : 0 < x*W := mul_pos hx' hW
  have hd'' : (d:ℝ) ≤ 25*(x*W) :=
    hd'.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hW.le hx) (by norm_num))
  refine ⟨Nat.cast_pos.mp ((mul_pos ha hXY).trans_le hlo),
    ⟨(le_div_iff₀ hXY).mpr hlo, (div_le_iff₀ hXY).mpr ?_⟩,
    ⟨(le_div_iff₀ hXY).mpr ?_, (div_le_iff₀ hXY).mpr ?_⟩⟩
  · nlinarith [mul_pos (by norm_num : (0:ℝ)<25) hXY]
  · push_cast
    linarith
  · push_cast
    linarith

end
end ArtinMatthews
