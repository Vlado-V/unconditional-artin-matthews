module

public import ArtinMatthews.SpectralCompactLaplaceCoshShift
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

def spectralABLCoshHeightWeight (b r u : ℝ) : ℝ :=
  Real.exp (r*|u|)/(1+b*Real.sinh |u|)^3

/-- The logarithmic height mass is uniform down to the endpoint order. -/
theorem spectralABLCoshHeightWeight_integral (b r : ℝ) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    Integrable (spectralABLCoshHeightWeight b r) ∧
      (∫ u : ℝ, spectralABLCoshHeightWeight b r u) ≤
        2*(1+Real.log (4/b))*Real.exp (r*Real.log (4/b)) := by
  let K := spectralABLCoshHeightWeight b r
  let L := Real.log (4/b)
  let E := Real.exp (r*L)
  have hFour : 4 ≤ (4 : ℝ)/b := (le_div_iff₀ hb).mpr (by linarith)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLexp : Real.exp L = 4/b := Real.exp_log (by positivity)
  have hr₃ : r-3 < 0 := by linarith
  have hden (u : ℝ) : 1 ≤ 1+b*Real.sinh |u| :=
    le_add_of_nonneg_right (mul_nonneg hb.le (Real.sinh_nonneg_iff.mpr (abs_nonneg _)))
  have hK : Continuous K := by
    unfold K spectralABLCoshHeightWeight
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (r*|u|))).div
      (by fun_prop) (fun u => (pow_pos (zero_lt_one.trans_le (hden u)) _).ne')
  have hK0 (u : ℝ) : 0 ≤ K u :=
    div_nonneg (Real.exp_nonneg _) (pow_nonneg (zero_le_one.trans (hden u)) _)
  have hsmall (u : ℝ) (hu : u ∈ Ioc 0 L) : K u ≤ E := by
    calc
      _ ≤ Real.exp (r*|u|) := div_le_self (Real.exp_nonneg _) (one_le_pow₀ (hden u))
      _ ≤ _ := by
        rw [abs_of_pos hu.1]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hr)
  have htail (u : ℝ) (hu : L < u) : K u ≤ (4/b)^3*Real.exp ((r-3)*u) := by
    have hu0 : 0 ≤ u := hL.trans hu.le
    have hEu : 2 ≤ Real.exp u := (by linarith : (2 : ℝ) ≤ 4/b).trans
      (hLexp ▸ Real.exp_le_exp.mpr hu.le)
    have hS : Real.exp u/4 ≤ Real.sinh u := by
      rw [Real.sinh_eq]
      linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu0)]
    have hD : b*Real.exp u/4 ≤ 1+b*Real.sinh u := by
      calc
        _ = b*(Real.exp u/4) := by ring
        _ ≤ b*Real.sinh u := mul_le_mul_of_nonneg_left hS hb.le
        _ ≤ _ := le_add_of_nonneg_left zero_le_one
    change Real.exp (r*|u|)/(1+b*Real.sinh |u|)^3 ≤ _
    rw [abs_of_nonneg hu0]
    calc
      _ ≤ Real.exp (r*u)/(b*Real.exp u/4)^3 :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity)
          (pow_le_pow_left₀ (by positivity) hD _)
      _ = _ := by
        rw [show (r-3)*u = r*u-(3 : ℕ)*u by push_cast; ring,
          Real.exp_sub,Real.exp_nat_mul,div_pow,mul_pow]
        field_simp [hb.ne',(Real.exp_pos u).ne'] <;> ring
  have hI₀ : IntegrableOn K (Ioc 0 L) :=
    (hK.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hM : IntegrableOn (fun u : ℝ => (4/b)^3*Real.exp ((r-3)*u)) (Ioi L) :=
    (integrableOn_exp_mul_Ioi hr₃ L).const_mul _
  have hI₁ : IntegrableOn K (Ioi L) := by
    apply hM.mono' hK.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (hK0 u)]
    exact htail u hu
  have hI : IntegrableOn K (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hL]
    exact hI₀.union hI₁
  have hneg : IntegrableOn K (Iic (0 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun u : ℝ => -u) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def,neg_preimage,neg_Iic,neg_zero]
    have he : (fun u : ℝ => K (-u)) = K := by funext u; simp only [K,spectralABLCoshHeightWeight,abs_neg]
    rw [he]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hI
  have hIall : Integrable K := by
    simpa only [Iic_union_Ioi,integrableOn_univ] using hneg.union hI
  have hsmall_int : (∫ u in Ioc (0 : ℝ) L, K u) ≤ L*E := by
    have hC : IntegrableOn (fun _ : ℝ => E) (Ioc (0 : ℝ) L) :=
      integrableOn_const (by simp [Real.volume_Ioc])
    calc
      _ ≤ ∫ _u in Ioc (0 : ℝ) L, E :=
        setIntegral_mono_on hI₀ hC measurableSet_Ioc hsmall
      _ = _ := by
        rw [setIntegral_const,Measure.real,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal hL,smul_eq_mul]
  have htail_int : (∫ u in Ioi L, K u) ≤ E := by
    calc
      _ ≤ ∫ u in Ioi L, (4/b)^3*Real.exp ((r-3)*u) :=
        setIntegral_mono_on hI₁ hM measurableSet_Ioi (fun u hu => htail u hu)
      _ = E/(3-r) := by
        rw [integral_const_mul,integral_exp_mul_Ioi hr₃,
          show (r-3)*L = r*L-(3 : ℕ)*L by push_cast; ring,Real.exp_sub,Real.exp_nat_mul,hLexp]
        dsimp [E]
        field_simp [hb.ne',hr₃.ne,show (3 : ℝ)-r ≠ 0 by linarith]
        ring
      _ ≤ E := div_le_self (Real.exp_nonneg _) (by linarith)
  have habs : (fun u : ℝ => K |u|) = K := by
    funext u
    simp only [K,spectralABLCoshHeightWeight,abs_abs]
  refine ⟨hIall,?_⟩
  change (∫ u : ℝ, K u) ≤ 2*(1+L)*E
  rw [← habs,integral_comp_abs,← Ioc_union_Ioi_eq_Ioi hL,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI₀ hI₁]
  calc
    _ ≤ 2*(L*E+E) := mul_le_mul_of_nonneg_left (add_le_add hsmall_int htail_int) (by norm_num)
    _ = _ := by ring

end
end ArtinMatthews
