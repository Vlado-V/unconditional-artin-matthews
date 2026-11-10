module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt
public import OAI.RepresentationTheory.Weil.Local.SquareBall
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Norm Chart Operations -/

namespace OAI.RepresentationTheory.Weil.Local.NormChartOperations.Construction

noncomputable section

/-! Multiplication, inversion, and squaring in the local rational norm-one coordinates. -/

variable {k : Type*} [Field k]

theorem quadraticNormChart_inv (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k) :
    (QuadraticNormAt.Construction.quadraticNormChart h t)⁻¹ = QuadraticNormAt.Construction.quadraticNormChart h (-t) := by
  apply Subtype.ext
  apply Prod.ext <;> simp [QuadraticNormAt.Construction.quadraticNormChart, QuadraticNormAt.Construction.QuadraticNormOne.inv_val, neg_div]

theorem quadraticNormChart_mul (h : ¬ ∃ r : k, r ^ 2 = -1) (t u : k)
    (htu : 1 - t * u ≠ 0) :
    QuadraticNormAt.Construction.quadraticNormChart h t * QuadraticNormAt.Construction.quadraticNormChart h u =
      QuadraticNormAt.Construction.quadraticNormChart h ((t + u) / (1 - t * u)) := by
  have hd : 1 + ((t + u) / (1 - t * u)) ^ 2 =
      (1 + t ^ 2) * (1 + u ^ 2) / (1 - t * u) ^ 2 := by
    field_simp
    ring
  apply Subtype.ext
  apply Prod.ext
  · change (1 - t ^ 2) / (1 + t ^ 2) * ((1 - u ^ 2) / (1 + u ^ 2)) -
        (2 * t / (1 + t ^ 2)) * (2 * u / (1 + u ^ 2)) =
      (1 - ((t + u) / (1 - t * u)) ^ 2) / (1 + ((t + u) / (1 - t * u)) ^ 2)
    rw [hd]
    field_simp [QuadraticNormAt.Construction.one_add_sq_ne_zero h t, QuadraticNormAt.Construction.one_add_sq_ne_zero h u]
    ring
  · change (1 - t ^ 2) / (1 + t ^ 2) * (2 * u / (1 + u ^ 2)) +
        (2 * t / (1 + t ^ 2)) * ((1 - u ^ 2) / (1 + u ^ 2)) =
      (2 * ((t + u) / (1 - t * u))) / (1 + ((t + u) / (1 - t * u)) ^ 2)
    rw [hd]
    field_simp [QuadraticNormAt.Construction.one_add_sq_ne_zero h t, QuadraticNormAt.Construction.one_add_sq_ne_zero h u]
    ring

theorem quadraticNormChart_sq (h : ¬ ∃ r : k, r ^ 2 = -1) (t : k)
    (ht : 1 - t ^ 2 ≠ 0) :
    QuadraticNormAt.Construction.quadraticNormChart h t ^ 2 = QuadraticNormAt.Construction.quadraticNormChart h (SquareBall.Construction.normOneSquareCoordinate t) := by
  rw [pow_two, quadraticNormChart_mul h t t (by simpa only [pow_two] using ht)]
  congr 1
  dsimp [SquareBall.Construction.normOneSquareCoordinate]
  ring

theorem one_sub_mul_norm_eq_one
    {k : Type*} [NormedField k] [IsUltrametricDist k] (t u : k)
    (ht : ‖t‖ < 1) (hu : ‖u‖ < 1) : ‖1 - t * u‖ = 1 := by
  have hp : ‖-(t * u)‖ < ‖(1 : k)‖ := by
    rw [norm_neg, norm_mul, norm_one]
    exact (mul_le_of_le_one_right (norm_nonneg t) hu.le).trans_lt ht
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hp.ne',
    max_eq_left hp.le, norm_one]

theorem norm_normChart_product_coordinate_le
    {k : Type*} [NormedField k] [IsUltrametricDist k] (t u : k)
    (ht : ‖t‖ < 1) (hu : ‖u‖ < 1) :
    ‖(t + u) / (1 - t * u)‖ ≤ max ‖t‖ ‖u‖ := by
  rw [norm_div, one_sub_mul_norm_eq_one t u ht hu, div_one]
  exact IsUltrametricDist.norm_add_le_max t u

end

end OAI.RepresentationTheory.Weil.Local.NormChartOperations.Construction
