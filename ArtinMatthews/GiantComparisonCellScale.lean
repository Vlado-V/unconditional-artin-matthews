module

public import ArtinMatthews.GiantComparisonCellGeometry
public import ArtinMatthews.IdealLogCellCount
public import ArtinMatthews.IdealProductDyadicBounds
public import ArtinMatthews.MarkedProgressionGrowth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Nonempty occupied comparison cells have the scales needed for
the rational multiplier and the centered endpoint energy. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantComparisonCellOrigin_source_geometry (c d C : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ {I : Type} [Fintype I] [DecidableEq I],
      ∀ (P : I → Finset ℕ) (i : I), (∀ j p, p ∈ P j → p.Prime) →
      (∀ j p, p ∈ P j → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
      (Fintype.card I : ℝ) ≤ C * Real.log L →
      ∀ h : ℝ, 0 < h → Real.exp h ≤ 2 → ∀ j ∈ idealLogCells P h,
        let U := giantComparisonCellOrigin h j
        0 < U ∧ Real.exp (L^c)/4 ≤ (U : ℝ) ∧
          (U : ℝ) ≤ Real.exp (C * Real.log L * L^d) ∧
          Real.log ((4*U : ℕ) : ℝ) ≤ L^(d+2) := by
  have hfast := (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hc)).eventually_ge_atTop 4
  filter_upwards [hfast, eventually_ge_atTop (max 2 (max (2*C) (2*Real.log 4)))] with L hfast hL
  change 4 ≤ Real.exp (L^c) at hfast
  have hL1 : 1 ≤ L := by have := (le_max_left _ _).trans hL; linarith
  have hLp := zero_lt_one.trans_le hL1
  have hLC : 2*C ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLlog : 2*Real.log 4 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  intro I _ _ P i hP hpr hcard h hh hexp j hj
  obtain ⟨a,_,ha⟩ := mem_image.mp hj
  let U := giantComparisonCellOrigin h j
  have hlo : Real.exp (L^c) ≤ (idealSelectedProduct a : ℝ) :=
    ((hpr i _ (a i).property).1).trans (by exact_mod_cast idealSelectedProduct_ge_prime P hP a i)
  obtain ⟨hUlo,hUprod,_⟩ := giantComparisonCellOrigin_bounds P hh hexp j a ha hfast hlo
  have hUr : 0 < (U : ℝ) := (by positivity : 0 < Real.exp (L^c)/4).trans_le hUlo
  have hUpos : 0 < U := by exact_mod_cast hUr
  have hUprod' : (U : ℝ) ≤ idealSelectedProduct a := by exact_mod_cast hUprod
  have hlogU : Real.log (U : ℝ) ≤ C * Real.log L * L^d := by
    refine (Real.log_le_log hUr hUprod').trans ?_
    exact (idealSelectedProduct_log_le P hP (fun j p hp => (hpr j p hp).2) a).trans
      (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hLp.le _))
  refine ⟨hUpos,hUlo,(Real.log_le_iff_le_exp hUr).mp hlogU,?_⟩
  have hCp : C * Real.log L ≤ C*L := mul_le_mul_of_nonneg_left (Real.log_le_self hLp.le) hC
  have hpow : 1 ≤ L^d := Real.one_le_rpow hL1 hd
  have hpow' : L^(d+2) = L^d * L^2 := by rw [Real.rpow_add hLp, Real.rpow_two]
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hUr.ne', hpow']
  calc
    _ ≤ Real.log 4 + (C*L)*L^d :=
      add_le_add_right (hlogU.trans (mul_le_mul_of_nonneg_right hCp
        (Real.rpow_nonneg hLp.le _))) _
    _ ≤ (L/2)*L^d + ((L/2)*L)*L^d := by
      apply add_le_add
      · exact (show Real.log 4 ≤ L/2 by linarith).trans (le_mul_of_one_le_right (by positivity) hpow)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hLp.le)
          (Real.rpow_nonneg hLp.le _)
    _ ≤ L^d * L^2 := by
      have h : 0 ≤ L^d * (L*(L-1)) := mul_nonneg (Real.rpow_nonneg hLp.le _)
        (mul_nonneg hLp.le (sub_nonneg.mpr hL1))
      nlinarith only [h]

theorem giantComparisonCellScale_subpower (C d ε : ℝ) (hC : 0 ≤ C)
    (hd : d < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (C * Real.log (Real.log x) * (Real.log x)^d) ≤ x^ε := by
  let η := (1-d)/2
  have hη : 0 < η := by dsimp [η]; linarith
  have hsum : η+d < 1 := by dsimp [η]; linarith
  have hlog := (isLittleO_log_rpow_atTop hη).bound (show (0:ℝ) < 1 by norm_num)
  filter_upwards [Real.tendsto_log_atTop.eventually hlog,
    marked_sublinear_log_exp_le_rpow_eventually (η+d) C ε hsum hε,
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hlog hpow hL
  let L := Real.log x
  change ‖Real.log L‖ ≤ (1 : ℝ)*‖L^η‖ at hlog
  have hLp : 0 < L := hL
  have hp : 0 ≤ L^η := Real.rpow_nonneg hLp.le η
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hp] at hlog
  have hlog' : Real.log L ≤ L^η := (le_abs_self _).trans hlog
  refine le_trans (Real.exp_le_exp.mpr ?_) hpow
  change C*Real.log L*L^d ≤ C*L^(η+d)
  rw [Real.rpow_add hL, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog' hC)
    (Real.rpow_nonneg hL.le _)

end
end ArtinMatthews
