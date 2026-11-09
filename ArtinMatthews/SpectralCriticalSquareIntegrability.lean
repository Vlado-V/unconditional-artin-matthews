module

public import ArtinMatthews.SpectralEisensteinCriticalPoleRemoval
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine square-integrable trace on the critical line cannot carry a
meromorphic pole, including at the endpoint of the positive spectral ray. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace ArtinMatthews

theorem eisensteinCriticalPoint_norm_sub (t u : ℝ) :
    ‖eisensteinCriticalPoint t-eisensteinCriticalPoint u‖=|t-u| := by
  have h : eisensteinCriticalPoint t-eisensteinCriticalPoint u=((t-u:ℝ):ℂ)*Complex.I := by
    simp only [eisensteinCriticalPoint,Complex.ofReal_sub]
    ring
  rw [h,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]

theorem spectralMeromorphic_order_critical_nonneg_of_sq_integrable (f : ℂ → ℂ)
    (t : ℝ) (ht : 0≤t) (hm : MeromorphicAt f (eisensteinCriticalPoint t))
    (hi : IntegrableOn (fun u => ‖f (eisensteinCriticalPoint u)‖^2) (Ioi 0)) :
    0 ≤ meromorphicOrderAt f (eisensteinCriticalPoint t) := by
  by_contra hn
  let s := eisensteinCriticalPoint t
  have ho : meromorphicOrderAt f s < 0 := lt_of_not_ge hn
  have htop : meromorphicOrderAt f s ≠ ⊤ := ne_of_lt (ho.trans (by simp))
  let m := (meromorphicOrderAt f s).untop htop
  have he : (m:WithTop ℤ)=meromorphicOrderAt f s := WithTop.coe_untop _ htop
  have hneg : m < 0 := by rw [← he] at ho; exact_mod_cast ho
  obtain ⟨g,hg,hg0,hgEq⟩ := (meromorphicOrderAt_eq_int_iff hm).mp he.symm
  let c := ‖g s‖/2
  have hc : 0<c := half_pos (norm_pos_iff.mpr hg0)
  have hc' : c<‖g s‖ := by dsimp [c] at hc ⊢; linarith
  have hcont : ContinuousAt (fun u : ℝ => g (eisensteinCriticalPoint u)) t :=
    hg.continuousAt.comp (f:=eisensteinCriticalPoint) eisensteinCriticalPoint_continuous.continuousAt
  have hlow : ∀ᶠ u in 𝓝 t,c<‖g (eisensteinCriticalPoint u)‖ :=
    hcont.norm.eventually_const_lt hc'
  have hright : 𝓝[>] t ≤ 𝓝[≠] t :=
    nhdsWithin_mono t (fun u hu => show u≠t from ne_of_gt hu)
  have hnear : ∀ᶠ u in 𝓝[>] t,
      f (eisensteinCriticalPoint u)=(eisensteinCriticalPoint u-s)^m • g (eisensteinCriticalPoint u) ∧
        c<‖g (eisensteinCriticalPoint u)‖ :=
    (((eisensteinCriticalPoint_tendsto_punctured t).eventually hgEq).filter_mono hright).and
      (hlow.filter_mono nhdsWithin_le_nhds)
  obtain ⟨a,ha,hA⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let d := min (a-t) 1
  have hd : 0<d := lt_min (sub_pos.mpr ha) zero_lt_one
  have hD : Ioo t (t+d)⊆Ioi 0 := fun _ hu => ht.trans_lt hu.1
  have hmeas : Measurable (fun u : ℝ => c^2*(u-t)^(-2:ℝ)) := by fun_prop
  have hsmall : IntegrableOn (fun u : ℝ => c^2*(u-t)^(-2:ℝ)) (Ioo t (t+d)) := by
    apply (hi.mono_set hD).mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioo] with u hu
    have hu0 := sub_pos.mpr hu.1
    have huA : u∈Ioo t a := ⟨hu.1,hu.2.trans_le (by dsimp [d]; linarith [min_le_left (a-t) 1])⟩
    have hu1 : u-t≤1 := by
      have h := min_le_right (a-t) (1:ℝ)
      change d≤1 at h
      linarith [hu.2]
    obtain ⟨hf,hgc⟩ := hA huA
    have hmle : (m:ℝ)≤ -1 := by exact_mod_cast (show m≤ -1 by omega)
    have hpow : (u-t)^(-1:ℝ)≤(u-t)^m := by
      rw [← Real.rpow_intCast]
      exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hmle
    have hnorm : c*(u-t)^(-1:ℝ)≤‖f (eisensteinCriticalPoint u)‖ := by
      rw [hf,norm_smul,norm_zpow,eisensteinCriticalPoint_norm_sub,abs_of_pos hu0]
      exact (mul_le_mul_of_nonneg_left hpow hc.le).trans
        (by simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hgc.le (zpow_nonneg hu0.le m))
    have hp2 : (u-t)^(-2:ℝ)=((u-t)^(-1:ℝ))^2 := by
      rw [← Real.rpow_two ((u-t)^(-1:ℝ)),← Real.rpow_mul hu0.le]
      norm_num
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hu0.le _)),hp2,← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc.le (Real.rpow_nonneg hu0.le _)) hnorm 2
  have hInt := (intervalIntegrable_iff_integrableOn_Ioo_of_le (show t≤t+d by linarith)).mpr hsmall
  have hshift : IntervalIntegrable (fun u : ℝ => c^2*u^(-2:ℝ)) volume 0 d := by
    simpa only [sub_self,add_sub_cancel_left,add_sub_cancel_right] using hInt.comp_add_right t
  have hpow := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hc.ne'))
    (fun u : ℝ => u^(-2:ℝ))).mp ((intervalIntegrable_iff_integrableOn_Ioo_of_le hd.le).mp hshift)
  have hbad := (intervalIntegral.integrableOn_Ioo_rpow_iff hd).mp hpow
  norm_num at hbad

end ArtinMatthews
