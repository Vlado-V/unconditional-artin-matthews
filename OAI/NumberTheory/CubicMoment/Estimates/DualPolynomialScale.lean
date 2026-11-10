module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicMoment.Estimates.HeckeDualContour
public import OAI.NumberTheory.CubicMoment.Estimates.MellinWeights
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace OAI

/-! The exact `sqrt(Z/J)` normalization of a retained dual norm block.
The normalized coefficients are independent of the character conductor. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma positive_cpow_phase {x : ℝ} (hx : 0 < x) (σ u : ℝ) :
    (x:ℂ)^((σ:ℂ)+(u:ℂ)*Complex.I) = (x^σ:ℝ)*mellinPhase u x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma dual_dyad_weight_identity {J x : ℝ} (hJ : 0 < J) (hx : 0 < x) :
    x^(-(1/2:ℝ)) = J^(-(1/2:ℝ))*(J/x)^(1/2:ℝ) := by
  rw [Real.div_rpow hJ.le hx.le,Real.rpow_neg hJ.le,Real.rpow_neg hx.le]
  field_simp [(Real.rpow_pos_of_pos hJ (1/2:ℝ)).ne']

lemma dual_dyad_weight_le_one {J x : ℝ} (hJ : 0 < J) (hx : J ≤ x) :
    (J/x)^(1/2:ℝ) ≤ 1 := by
  apply Real.rpow_le_one
  · exact div_nonneg hJ.le (hJ.le.trans hx)
  · exact (div_le_one (hJ.trans_le hx)).mpr hx
  · norm_num

/-- Extracting the inverse square-root dyadic length changes only the
fixed norm coefficients; the character remains in the same polynomial. -/
theorem finite_dual_dyad_rescale {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) {J : ℝ} (hJ : 0 < J) (hN : ∀ i ∈ S, 0 < N i) (u : ℝ) :
    finiteNormDirichlet S a N ((1/2:ℂ)-(u:ℂ)*Complex.I) =
      (J^(-(1/2:ℝ)):ℝ)*∑ i ∈ S,
        (a i*((J/N i)^(1/2:ℝ):ℝ))*mellinPhase u (N i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : -((1/2:ℂ)-(u:ℂ)*Complex.I) = ((-(1/2:ℝ)):ℂ)+(u:ℂ)*Complex.I := by
    push_cast
    ring
  change a i*(N i:ℂ)^(-((1/2:ℂ)-(u:ℂ)*Complex.I)) = _
  rw [he,← Complex.ofReal_neg,positive_cpow_phase (hN i hi) (-(1/2:ℝ)) u,dual_dyad_weight_identity hJ (hN i hi)]
  push_cast
  ring

lemma norm_dual_dyad_coefficient_le {J x : ℝ} (hJ : 0 < J) (hx : J ≤ x) (a : ℂ) :
    ‖a*((J/x)^(1/2:ℝ):ℝ)‖ ≤ ‖a‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (div_nonneg hJ.le (hJ.le.trans hx)) _)]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (dual_dyad_weight_le_one hJ hx)

end CubicFirstMoment

end

end OAI
