module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralCauchyMellin
public import ArtinMatthews.SpectralDampedKMellin
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

/-! Absolute Mellin Fubini for the Stieltjes transform of the damped K kernel. -/

namespace ArtinMatthews

open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology

noncomputable section

def spectralStieltjesKWeight (r y : ℝ) : ℂ :=
  (y : ℂ) ^ (-(1 / 2 : ℂ)) *
    (Complex.exp (-(y : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) y)

def spectralStieltjesK (r x : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), spectralStieltjesKWeight r y / ((y + x : ℝ) : ℂ)

theorem spectralStieltjesKWeight_integrable (r : ℝ) :
    IntegrableOn (spectralStieltjesKWeight r) (Ioi (0 : ℝ)) := by
  have hs : |((r : ℂ) * Complex.I).re| < (1 / 2 : ℂ).re := by
    norm_num [Complex.mul_re, Complex.div_re]
  have h := spectralDampedK_mellin_integrable ((r : ℂ) * Complex.I) (1 / 2) hs
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring] at h
  change IntegrableOn (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 : ℂ)) *
    (Complex.exp (-(y : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) y)) (Ioi (0 : ℝ))
  simpa only [mul_assoc] using h

private theorem spectralStieltjesKSlice_norm_le (r : ℝ) {a x y : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hy : 0 < y) :
    ‖spectralStieltjesKWeight r y / ((y + x : ℝ) : ℂ)‖ ≤
      ‖spectralStieltjesKWeight r y‖ * a⁻¹ := by
  have hxy : 0 < y + x := add_pos hy (ha.trans_le hax)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hxy.le, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hxy ha).mpr (by linarith)) (norm_nonneg _)

private theorem spectralStieltjesKSlice_aestronglyMeasurable (r x : ℝ) :
    AEStronglyMeasurable (fun y => spectralStieltjesKWeight r y / ((y + x : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hd : Measurable (fun y : ℝ => ((y + x : ℝ) : ℂ)) := by fun_prop
  exact ((spectralStieltjesKWeight_integrable r).aestronglyMeasurable.aemeasurable.fun_div
    hd.aemeasurable).aestronglyMeasurable

theorem spectralStieltjesK_slice_integrable (r : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => spectralStieltjesKWeight r y / ((y + x : ℝ) : ℂ)) (Ioi (0 : ℝ)) := by
  have hw := spectralStieltjesKWeight_integrable r
  apply (hw.norm.mul_const x⁻¹).mono'
  · exact spectralStieltjesKSlice_aestronglyMeasurable r x
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact spectralStieltjesKSlice_norm_le r hx le_rfl hy

theorem spectralStieltjesK_continuousAt (r : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (spectralStieltjesK r) x := by
  have hw := spectralStieltjesKWeight_integrable r
  unfold spectralStieltjesK
  apply continuousAt_of_dominated
    (bound := fun y => ‖spectralStieltjesKWeight r y‖ * (x / 2)⁻¹)
  · filter_upwards with u
    exact spectralStieltjesKSlice_aestronglyMeasurable r u
  · filter_upwards [Ioi_mem_nhds (half_lt_self hx)] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact spectralStieltjesKSlice_norm_le r (half_pos hx) hu.le hy
  · exact hw.norm.mul_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact continuousAt_const.div (by fun_prop)
      (Complex.ofReal_ne_zero.mpr (add_pos hy hx).ne')

private theorem stieltjesWeight_mul_power (r : ℝ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    spectralStieltjesKWeight r y * (y : ℂ) ^ (s - 1) =
      (y : ℂ) ^ ((s - 1 / 2) - 1) *
        (Complex.exp (-(y : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) y) := by
  have hpow : (y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-(1 / 2 : ℂ)) =
      (y : ℂ) ^ ((s - 1 / 2) - 1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
    congr 1
    ring
  rw [← hpow, spectralStieltjesKWeight]
  ring

private theorem stieltjesWeight_mul_power_integrable (r : ℝ) (s : ℂ) (hs : 1 / 2 < s.re) :
    IntegrableOn (fun y => spectralStieltjesKWeight r y * (y : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
  have hs' : |((r : ℂ) * Complex.I).re| < (s - 1 / 2).re := by
    norm_num [Complex.mul_re, Complex.sub_re, Complex.div_re]
    linarith
  have h := spectralDampedK_mellin_integrable ((r : ℂ) * Complex.I) (s - 1 / 2) hs'
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [stieltjesWeight_mul_power r s hy]
  ring

private theorem stieltjesMellin_pair_integrable (r : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) (hsh : s.re < 1) :
    Integrable (fun p : ℝ × ℝ => spectralStieltjesKWeight r p.1 *
      spectralCauchyMellinKernel s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs0 : 0 < s.re := by linarith
  have hW : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralStieltjesKWeight r p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (spectralStieltjesKWeight_integrable r).aestronglyMeasurable.comp_fst
  have hC : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralCauchyMellinKernel s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hp : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (s - 1)) := by fun_prop
    have hd : Measurable (fun p : ℝ × ℝ => ((p.1 + p.2 : ℝ) : ℂ)) := by fun_prop
    unfold spectralCauchyMellinKernel
    exact (hp.fun_div hd).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralStieltjesKWeight r p.1 *
      spectralCauchyMellinKernel s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hW.fun_mul hC
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change IntegrableOn (fun x => spectralStieltjesKWeight r y * spectralCauchyMellinKernel s y x)
      (Ioi (0 : ℝ))
    exact (spectralCauchyMellinKernel_integrable s hs0 hsh hy).const_mul _
  · apply ((stieltjesWeight_mul_power_integrable r s hs).norm.const_mul
      (∫ u : ℝ, ‖spectralBetaLogProfile s (1 - s) u‖)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change (∫ u : ℝ, ‖spectralBetaLogProfile s (1 - s) u‖) *
      ‖spectralStieltjesKWeight r y * (y : ℂ) ^ (s - 1)‖ =
      ∫ x in Ioi (0 : ℝ), ‖spectralStieltjesKWeight r y * spectralCauchyMellinKernel s y x‖
    simp only [norm_mul, integral_const_mul, spectralCauchyMellinKernel_norm_integral s hy]
    ring

private theorem stieltjesMellin_integral_y (r : ℝ) (s : ℂ) (x : ℝ) :
    (∫ y in Ioi (0 : ℝ), spectralStieltjesKWeight r y *
      spectralCauchyMellinKernel s y x) = (x : ℂ) ^ (s - 1) * spectralStieltjesK r x := by
  rw [spectralStieltjesK, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  unfold spectralCauchyMellinKernel
  ring

theorem spectralStieltjesK_hasMellin (r : ℝ) (s : ℂ) (hs : 1 / 2 < s.re) (hsh : s.re < 1) :
    HasMellin (spectralStieltjesK r) s
      (((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
        mellin (fun y : ℝ => Complex.exp (-(y : ℂ)) *
          schlafliBesselK ((r : ℂ) * Complex.I) y) (s - 1 / 2)) := by
  have hs0 : 0 < s.re := by linarith
  have hpair := stieltjesMellin_pair_integrable r s hs hsh
  constructor
  · simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, stieltjesMellin_integral_y r s] using
      hpair.integral_prod_right
  · calc
      mellin (spectralStieltjesK r) s =
          ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), spectralStieltjesKWeight r y *
            spectralCauchyMellinKernel s y x := by
        simp only [mellin, smul_eq_mul, stieltjesMellin_integral_y r s]
      _ = ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), spectralStieltjesKWeight r y *
            spectralCauchyMellinKernel s y x :=
        (integral_integral_swap (f := fun y x : ℝ => spectralStieltjesKWeight r y *
          spectralCauchyMellinKernel s y x) hpair).symm
      _ = _ := by
        rw [mellin, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        change (∫ x in Ioi (0 : ℝ), spectralStieltjesKWeight r y *
          spectralCauchyMellinKernel s y x) =
          ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
            ((y : ℂ) ^ ((s - 1 / 2) - 1) •
              (Complex.exp (-(y : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) y))
        rw [integral_const_mul, spectralCauchyMellinKernel_integral s hs0 hsh hy]
        simp only [smul_eq_mul]
        rw [← stieltjesWeight_mul_power r s hy]
        ring

end

end ArtinMatthews
