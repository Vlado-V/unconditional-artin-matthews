module

public import ArtinMatthews.SpectralGamma0EisensteinFourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Fubini on the actual compact period-one horocycle. -/
noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

def gamma0EisensteinHorizontalPoint (y : ℝ) (hy : 0<y) (x : ℝ) : UpperHalfPlane := ⟨⟨x,y⟩,hy⟩

theorem gamma0EisensteinHorizontalPoint_continuous (y : ℝ) (hy : 0<y) :
    Continuous (gamma0EisensteinHorizontalPoint y hy) := by
  have h : Continuous (fun x : ℝ => Complex.mk x y) := by
    convert! Complex.continuous_ofReal.add
      (continuous_const : Continuous (fun _ : ℝ => (y:ℂ)*Complex.I)) using 1
    funext x
    apply Complex.ext <;> simp
  exact h.upperHalfPlaneMk (fun _ => hy)

theorem gamma0EisensteinSummand_horizontal_continuous (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) (v : Gamma0EisensteinRows N) :
    Continuous (fun x => gamma0EisensteinSummand N s v (gamma0EisensteinHorizontalPoint y hy x)) :=
  (gamma0EisensteinSummand_continuous N s hs v).comp (gamma0EisensteinHorizontalPoint_continuous y hy)

theorem gamma0EisensteinSummand_horizontal_integrable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) (v : Gamma0EisensteinRows N) :
    IntegrableOn (fun x => gamma0EisensteinSummand N s v (gamma0EisensteinHorizontalPoint y hy x))
      (Ioc (0:ℝ) 1) :=
  (gamma0EisensteinSummand_horizontal_continuous N s hs y hy v).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem gamma0EisensteinSummand_integral_norm_summable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    Summable (fun v : Gamma0EisensteinRows N =>
      ∫ x in Ioc (0:ℝ) 1, ‖gamma0EisensteinSummand N s v (gamma0EisensteinHorizontalPoint y hy x)‖) := by
  have hK := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).image
    (gamma0EisensteinHorizontalPoint_continuous y hy)
  obtain ⟨u,hu,hb⟩ := gamma0EisensteinSummand_compact_majorant N s hs hK
  apply hu.of_nonneg_of_le (fun v => integral_nonneg (fun x => norm_nonneg _))
  intro v
  have hi := (gamma0EisensteinSummand_horizontal_integrable N s hs y hy v).norm
  have hc : IntegrableOn (fun _ : ℝ => u v) (Ioc (0:ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hle := integral_mono_ae hi hc (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hb v _ ⟨x,Ioc_subset_Icc_self hx,rfl⟩)
  simpa using hle

theorem gamma0Eisenstein_integral_eq_half_tsum_rows (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0EisensteinSlice N s y hy x) =
      (1/2:ℂ)*∑' v : Gamma0EisensteinRows N,
        ∫ x in (0:ℝ)..1, gamma0EisensteinSummand N s v (gamma0EisensteinHorizontalPoint y hy x) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  change (∫ x in Ioc (0:ℝ) 1, (1/2:ℂ)*∑' v : Gamma0EisensteinRows N,
    gamma0EisensteinSummand N s v (gamma0EisensteinHorizontalPoint y hy x))=_
  rw [integral_const_mul,← integral_tsum_of_summable_integral_norm
    (gamma0EisensteinSummand_horizontal_integrable N s hs y hy)
    (gamma0EisensteinSummand_integral_norm_summable N s hs y hy)]
  congr 1
  apply tsum_congr
  intro v
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

end ArtinMatthews
