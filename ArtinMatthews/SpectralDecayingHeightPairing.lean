module

public import ArtinMatthews.SpectralHeightPartialProfile
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! The diagonal height pairing of two actual decaying profiles is
absolutely integrable and respects the exhausting native cutoffs. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ArtinMatthews

theorem spectralDecayingHeightPairing_small_bound (P Q : SpectralDecayingHeightProfile)
    {y : ℝ} (hy : 0 < y) :
    ‖P.value y*Q.value y/y^2‖ ≤
      (P.bound*Q.bound)*y^(P.exponent+Q.exponent-2) := by
  rw [norm_div,norm_mul,Real.norm_of_nonneg (sq_nonneg y)]
  calc
    _ ≤ (P.bound*y^P.exponent)*(Q.bound*y^Q.exponent)/y^2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (P.small_bound y hy) (Q.small_bound y hy) (norm_nonneg _)
          (mul_nonneg P.bound_nonneg (Real.rpow_nonneg hy.le _))) (sq_nonneg y)
    _ = (P.bound*Q.bound)*(y^P.exponent*y^Q.exponent/y^2) := by ring
    _ = _ := by
      rw [Real.rpow_sub hy (P.exponent+Q.exponent) 2,
        Real.rpow_add hy P.exponent Q.exponent,Real.rpow_two]

theorem spectralDecayingHeightPairing_large_bound (P Q : SpectralDecayingHeightProfile)
    {y : ℝ} (hy : 0 < y) :
    ‖P.value y*Q.value y/y^2‖ ≤
      (P.bound*Q.bound)*y^(-P.exponent-Q.exponent-2) := by
  rw [norm_div,norm_mul,Real.norm_of_nonneg (sq_nonneg y)]
  calc
    _ ≤ (P.bound*y^(-P.exponent))*(Q.bound*y^(-Q.exponent))/y^2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (P.large_bound y hy) (Q.large_bound y hy) (norm_nonneg _)
          (mul_nonneg P.bound_nonneg (Real.rpow_nonneg hy.le _))) (sq_nonneg y)
    _ = (P.bound*Q.bound)*(y^(-P.exponent)*y^(-Q.exponent)/y^2) := by ring
    _ = _ := by
      rw [show -P.exponent-Q.exponent-2 = (-P.exponent+-Q.exponent)-2 by ring,
        Real.rpow_sub hy (-P.exponent+-Q.exponent) 2,
        Real.rpow_add hy (-P.exponent) (-Q.exponent),Real.rpow_two]

theorem spectralDecayingHeightPairing_integrable (P Q : SpectralDecayingHeightProfile) :
    IntegrableOn (fun y : ℝ => P.value y*Q.value y/y^2) (Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn (fun y : ℝ => P.value y*Q.value y/y^2) (Ioi (0 : ℝ)) :=
    (P.smooth.continuousOn.mul Q.smooth.continuousOn).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 hy.ne')
  have hnear : IntegrableOn (fun y : ℝ => (P.bound*Q.bound)*y^(P.exponent+Q.exponent-2))
      (Ioc (0 : ℝ) 1) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (by linarith [P.exponent_gt_one,Q.exponent_gt_one] : -1 < P.exponent+Q.exponent-2)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h).const_mul _
  have hfar : IntegrableOn (fun y : ℝ => (P.bound*Q.bound)*y^(-P.exponent-Q.exponent-2))
      (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt
      (by linarith [P.exponent_gt_one,Q.exponent_gt_one] : -P.exponent-Q.exponent-2 < -1)
      zero_lt_one).const_mul _
  have hn : IntegrableOn (fun y : ℝ => P.value y*Q.value y/y^2) (Ioc (0 : ℝ) 1) := by
    apply hnear.mono' ((hcont.mono
      (show Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from fun _ hy => hy.1)).aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact spectralDecayingHeightPairing_small_bound P Q hy.1
  have hf : IntegrableOn (fun y : ℝ => P.value y*Q.value y/y^2) (Ioi (1 : ℝ)) := by
    apply hfar.mono' ((hcont.mono
      (show Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) from by
        intro y hy
        exact lt_trans (by norm_num : (0 : ℝ) < 1) (show (1 : ℝ) < y from hy))).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact spectralDecayingHeightPairing_large_bound P Q (lt_trans (by norm_num : (0 : ℝ) < 1) hy)
  have hu := hn.union hf
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at hu

theorem spectralDecayingHeightPairing_cutoff_tendsto (P Q : SpectralDecayingHeightProfile) :
    Tendsto (fun K : ℕ => cuspFourierHeightPairing (spectralHeightProfilePartial K P.value) Q.value)
      atTop (𝓝 (cuspFourierHeightPairing P.value Q.value)) := by
  have hi := spectralDecayingHeightPairing_integrable P Q
  unfold cuspFourierHeightPairing
  apply tendsto_integral_of_dominated_convergence (fun y : ℝ => ‖P.value y*Q.value y/y^2‖)
  · intro K
    have hcont : ContinuousOn
        (fun y : ℝ => spectralHeightProfilePartial K P.value y*Q.value y/y^2) (Ioi (0 : ℝ)) :=
      ((spectralHeightProfilePartial_contDiff K P.value P.smooth).continuous.continuousOn.mul
        Q.smooth.continuousOn).div (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 hy.ne')
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · exact hi.norm
  · intro K
    filter_upwards with y
    rw [spectralHeightProfilePartial_apply]
    have he : spectralHeightAnnularPartial K y*P.value y*Q.value y/y^2 =
        spectralHeightAnnularPartial K y*(P.value y*Q.value y/y^2) := by ring
    rw [he,norm_mul,Real.norm_of_nonneg (spectralHeightAnnularPartial_bounds K y).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (spectralHeightAnnularPartial_bounds K y).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralHeightAnnularPartial_eventually_one hy] with K hK
    rw [spectralHeightProfilePartial_apply,hK,one_mul]

end ArtinMatthews
