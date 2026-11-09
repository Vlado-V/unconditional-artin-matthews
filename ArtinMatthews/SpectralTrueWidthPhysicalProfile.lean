module

public import ArtinMatthews.SpectralHeightPartialProfile
public import ArtinMatthews.SpectralKLHeightPhysicalTest


set_option backward.privateInPublic true
@[expose] public section

/-! Literal physical profiles of the native decaying height data, with
their cutoff and power bounds in the actual true-width coordinates. -/

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ArtinMatthews

theorem spectralKLHeightPhysicalTest_partial_width (q w : ℝ) (K : ℕ) (ρ : ℝ → ℝ) :
    spectralKLHeightPhysicalTest q (fun y => spectralHeightProfilePartial K ρ (w*y)) =
      spectralWeylProfileCutoff (w/q) K (spectralKLHeightPhysicalTest q (fun y => ρ (w*y))) := by
  funext x
  unfold spectralKLHeightPhysicalTest spectralKLHeightBaseTest spectralWeylProfileCutoff
  dsimp only
  rw [spectralHeightProfilePartial_apply]
  have he : w*(x/q) = (w/q)*x := by ring
  rw [he]
  push_cast
  ring

theorem spectralKLHeightPhysicalTest_width_continuousOn {q w : ℝ}
    (hq : 0 < q) (hw : 0 < w) (ρ : ℝ → ℝ)
    (hρ : ContinuousOn ρ (Ioi (0 : ℝ))) :
    ContinuousOn (spectralKLHeightPhysicalTest q (fun y => ρ (w*y))) (Ioi (0 : ℝ)) := by
  intro x hx
  have hy : 0 < x/q := div_pos hx hq
  have hρx : ContinuousAt ρ (w*(x/q)) := (hρ _ (mul_pos hw hy)).continuousAt (Ioi_mem_nhds (mul_pos hw hy))
  apply ContinuousAt.continuousWithinAt
  unfold spectralKLHeightPhysicalTest spectralKLHeightBaseTest
  have harg : ContinuousAt (fun z : ℝ => z/q) x := by fun_prop
  have hwarg : ContinuousAt (fun z : ℝ => w*(z/q)) x := by fun_prop
  have hcomp : ContinuousAt (fun z : ℝ => ρ (w*(z/q))) x :=
    ContinuousAt.comp (f := fun z : ℝ => w*(z/q)) hρx hwarg
  have hnum : ContinuousAt (fun z : ℝ => ((ρ (w*(z/q))*Real.sqrt (z/q) : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp
      (hcomp.mul (Real.continuous_sqrt.continuousAt.comp harg))
  have hden : ContinuousAt (fun z : ℝ => ((z/q : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp harg
  exact hnum.div hden (Complex.ofReal_ne_zero.mpr hy.ne')

theorem spectralKLHeightPhysicalTest_width_measurable {q w : ℝ}
    (hq : 0 < q) (hw : 0 < w) (ρ : ℝ → ℝ)
    (hρ : ContinuousOn ρ (Ioi (0 : ℝ))) :
    Measurable (spectralKLHeightPhysicalTest q (fun y => ρ (w*y))) := by
  classical
  have hc := spectralKLHeightPhysicalTest_width_continuousOn hq hw ρ hρ
  have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) measurableSet_Ioi
  convert hm using 1
  funext x
  by_cases hx : 0 < x
  · exact (piecewise_eq_of_mem (Ioi (0 : ℝ)) _ _ hx).symm
  · have hy : x/q ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hx) hq.le
    simp only [piecewise_eq_of_notMem (Ioi (0 : ℝ)) _ _ hx,
      spectralKLHeightPhysicalTest,spectralKLHeightBaseTest,Real.sqrt_eq_zero_of_nonpos hy,
      mul_zero,Complex.ofReal_zero,zero_div]

theorem spectralHeight_power_physical_factor {x q w : ℝ}
    (hx : 0 < x) (hq : 0 < q) (hw : 0 < w) (p C : ℝ) :
    (C*(w*(x/q))^p)*Real.sqrt (x/q)/(x/q) =
      (C*w^p/q^(p-1/2))*x^(p-1/2) := by
  have hy : 0 < x/q := div_pos hx hq
  have hs : Real.sqrt (x/q) ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have he : (x/q)^p*Real.sqrt (x/q)/(x/q) = (x/q)^(p-1/2) := by
    rw [Real.rpow_sub hy,← Real.sqrt_eq_rpow]
    field_simp
    rw [Real.sq_sqrt hy.le]
    field_simp
  rw [Real.mul_rpow hw.le hy.le]
  calc
    _ = (C*w^p)*((x/q)^p*Real.sqrt (x/q)/(x/q)) := by ring
    _ = (C*w^p)*(x/q)^(p-1/2) := by rw [he]
    _ = _ := by rw [Real.div_rpow hx.le hq.le]; ring

theorem spectralKLHeightPhysicalTest_decaying_power {q w : ℝ}
    (hq : 0 < q) (hw : 0 < w) (P : SpectralDecayingHeightProfile) {x : ℝ} (hx : 0 < x) :
    ‖spectralKLHeightPhysicalTest q (fun y => P.value (w*y)) x‖ ≤
      (P.bound*w^P.exponent/q^(P.exponent-1/2))*x^(P.exponent-1/2) := by
  have hy : 0 < x/q := div_pos hx hq
  have hp := P.small_bound (w*(x/q)) (mul_pos hw hy)
  have hnorm : ‖spectralKLHeightPhysicalTest q (fun y => P.value (w*y)) x‖ =
      ‖P.value (w*(x/q))‖*Real.sqrt (x/q)/(x/q) := by
    simp only [spectralKLHeightPhysicalTest,spectralKLHeightBaseTest,norm_div,
      Complex.norm_real,norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.norm_of_nonneg hy.le]
  rw [hnorm]
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)) hy.le).trans_eq ?_
  exact spectralHeight_power_physical_factor hx hq hw P.exponent P.bound

end ArtinMatthews
