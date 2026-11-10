module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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

/-! A genuinely bounded inverse-height-square multiplier, agreeing with the
Euclidean forcing coefficient on every chart above the chosen positive height. -/

noncomputable section
open Set

namespace ArtinMatthews

def spectralEllipticInverseHeight (a : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  1 / (max a (x 1))^2

theorem spectralEllipticInverseHeight_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (spectralEllipticInverseHeight a) :=
  continuous_const.div ((continuous_const.max (continuous_apply 1)).pow 2)
    (fun x => ne_of_gt (sq_pos_of_pos (ha.trans_le (le_max_left a (x 1)))))

theorem spectralEllipticInverseHeight_nonneg (a : ℝ) (x : Fin 2 → ℝ) :
    0 ≤ spectralEllipticInverseHeight a x := by
  unfold spectralEllipticInverseHeight
  positivity

theorem spectralEllipticInverseHeight_bound {a : ℝ} (ha : 0 < a) (x : Fin 2 → ℝ) :
    |spectralEllipticInverseHeight a x| ≤ 1/a^2 := by
  rw [abs_of_nonneg (spectralEllipticInverseHeight_nonneg a x)]
  exact one_div_le_one_div_of_le (sq_pos_of_pos ha)
    ((sq_le_sq₀ ha.le (ha.le.trans (le_max_left a (x 1)))).mpr (le_max_left a (x 1)))

theorem spectralEllipticInverseHeight_eq {a : ℝ} {x : Fin 2 → ℝ} (hx : a ≤ x 1) :
    spectralEllipticInverseHeight a x = 1/(x 1)^2 := by
  simp only [spectralEllipticInverseHeight,max_eq_right hx]

end ArtinMatthews
