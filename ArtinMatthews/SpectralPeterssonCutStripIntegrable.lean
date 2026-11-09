module

public import ArtinMatthews.SpectralPeterssonCutGammaEnvelope
public import ArtinMatthews.SpectralPeterssonCutPeriodization


set_option backward.privateInPublic true
@[expose] public section

/-! The literal sharply truncated seed pairing is absolutely integrable
against a bounded Petersson-weighted cusp function, also at weight two. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

theorem spectralPeterssonCutStrip_coordinates (k : ℕ) (n : ℕ+) (A : ℝ)
    (F : UpperHalfPlane → ℂ) :
    (fun z => UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed n A) F z) =
      fun z => ((Ioc (0 : ℝ) 1) ×ˢ (Ioi (A/(4*Real.pi*(n : ℝ))))).indicator
        (spectralPeterssonStripCoordinates k n F) (z.re,z.im) := by
  let r : ℝ := 4*Real.pi*(n : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  let δ := A/r
  let S := (Ioc (0 : ℝ) 1) ×ˢ Ioi δ
  let G := spectralPeterssonStripCoordinates k n F
  change (fun z => UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed n A) F z) =
    fun z => S.indicator G (z.re,z.im)
  funext z
  have hcut : A < 4*Real.pi*(n : ℝ)*z.im ↔ δ < z.im := by
    simpa only [δ,r,mul_comm] using (div_lt_iff₀ hr : A/r < z.im ↔ A < z.im*r).symm
  have hstrip : z ∈ hyperbolicCuspStrip 1 0 ↔ z.re ∈ Ioc (0 : ℝ) 1 := by
    change (z.re ∈ Ioc (0 : ℝ) 1 ∧ 0 < z.im) ↔ _
    simp only [z.im_pos,and_true]
  by_cases hx : z.re ∈ Ioc (0 : ℝ) 1
  · by_cases hy : δ < z.im
    · simp only [UpperHalfPlane.petersson,spectralPeterssonStripCutSeed,
        indicator_of_mem (hstrip.mpr hx),spectralPeterssonHeightCutSeed,if_pos (hcut.mpr hy)]
      rw [indicator_of_mem (show (z.re,z.im) ∈ S from ⟨hx,hy⟩)]
      simp only [G,spectralPeterssonStripCoordinates,spectralPeterssonCoordinatePoint_at,UpperHalfPlane.petersson]
    · have hz : (z.re,z.im) ∉ S := fun h => hy h.2
      simp only [UpperHalfPlane.petersson,spectralPeterssonStripCutSeed,
        indicator_of_mem (hstrip.mpr hx),spectralPeterssonHeightCutSeed,
        if_neg (fun h => hy (hcut.mp h)),map_zero,zero_mul,indicator_of_notMem hz]
  · have hz : (z.re,z.im) ∉ S := fun h => hx h.1
    simp only [UpperHalfPlane.petersson,spectralPeterssonStripCutSeed,
      indicator_of_notMem (fun h => hx (hstrip.mp h)),map_zero,zero_mul,indicator_of_notMem hz]


theorem spectralPeterssonCutCoordinates_weighted_integrable (k : ℕ) (hk : 2 ≤ k) (n : ℕ+)
    (δ : ℝ) (hδ : 0 < δ)
    (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ)
    (hbd : ∀ z, ‖F z‖*z.im^((k : ℝ)/2) ≤ M) :
    IntegrableOn (fun p : ℝ × ℝ => (p.2^2)⁻¹ • spectralPeterssonStripCoordinates k n F p)
      ((Ioc (0 : ℝ) 1) ×ˢ (Ioi δ)) (volume.prod volume) := by
  let S := (Ioc (0 : ℝ) 1) ×ˢ (Ioi δ)
  let U := {p : ℝ × ℝ | 0 < p.2}
  let G (p : ℝ × ℝ) := (p.2^2)⁻¹ • spectralPeterssonStripCoordinates k n F p
  let r := 2*Real.pi*(n : ℝ)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hr : 0 < r := mul_pos (mul_pos two_pos Real.pi_pos) hn
  have hγ : IntegrableOn (fun y : ℝ => y^((k : ℝ)/2-2)*Real.exp (-(r*y))) (Ioi δ) :=
    spectralPeterssonCutGammaEnvelope_integrable k hk r δ hr hδ
  have hEnv : IntegrableOn (fun p : ℝ × ℝ => M*(p.2^((k : ℝ)/2-2)*Real.exp (-(r*p.2)))) S
      (volume.prod volume) := by
    rw [IntegrableOn,← Measure.prod_restrict]
    let _ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
    have hx : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 1)) := integrable_const _
    simpa only [one_mul] using hx.mul_prod (hγ.const_mul M)
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hSU : S ⊆ U := fun _ hp => hδ.trans hp.2
  have hseed : Continuous (spectralHolomorphicCuspSeed (n : ℕ)) := by
    unfold spectralHolomorphicCuspSeed
    fun_prop
  have hP : ContinuousOn (spectralPeterssonStripCoordinates k n F) U :=
    (UpperHalfPlane.petersson_continuous (k : ℤ) hseed hF).continuousOn.comp
      spectralPeterssonCoordinatePoint_continuousOn (fun _ _ => Set.mem_univ _)
  have hInv : ContinuousOn (fun p : ℝ × ℝ => (p.2^2)⁻¹) U :=
    (continuous_snd.pow 2).continuousOn.inv₀ (fun _ hp => pow_ne_zero _ (ne_of_gt hp))
  have hG : ContinuousOn G U := hInv.smul hP
  refine hEnv.mono' ((hG.mono hSU).aestronglyMeasurable hS) ?_
  filter_upwards [ae_restrict_mem (μ := volume.prod volume) hS] with p hp
  let z := spectralPeterssonCoordinatePoint p
  have hy : 0 < p.2 := hδ.trans hp.2
  have hz : z.im = p.2 := spectralPeterssonCoordinatePoint_im p hy
  have hweight : (p.2^2)⁻¹*p.2^k = p.2^((k : ℝ)/2)*p.2^((k : ℝ)/2-2) := by
    rw [mul_comm,← div_eq_mul_inv,← Real.rpow_natCast,← Real.rpow_natCast,
      ← Real.rpow_sub hy,← Real.rpow_add hy]
    congr 1
    norm_num
    ring
  have hnorm : ‖G p‖ = (‖F z‖*p.2^((k : ℝ)/2))*(p.2^((k : ℝ)/2-2)*Real.exp (-(r*p.2))) := by
    dsimp only [G,spectralPeterssonStripCoordinates]
    rw [norm_smul,Real.norm_of_nonneg (by positivity),UpperHalfPlane.petersson]
    simp only [norm_mul,Complex.norm_conj,spectralHolomorphicCuspSeed_norm,zpow_natCast,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg (spectralPeterssonCoordinatePoint p).im_pos.le]
    change (p.2^2)⁻¹*(Real.exp (-(r*z.im))*‖F z‖*z.im^k) = _
    rw [hz,show (p.2^2)⁻¹*(Real.exp (-(r*p.2))*‖F z‖*p.2^k) =
      ‖F z‖*((p.2^2)⁻¹*p.2^k)*Real.exp (-(r*p.2)) by ring,hweight]
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right (by simpa only [hz] using hbd z)
    (mul_nonneg (Real.rpow_nonneg hy.le _) (Real.exp_nonneg _))

theorem spectralPeterssonCutStrip_integrable (k : ℕ) (hk : 2 ≤ k) (n : ℕ+)
    (A : ℝ) (hA : 0 < A) (F : UpperHalfPlane → ℂ) (hF : Continuous F) (M : ℝ)
    (hbd : ∀ z, ‖F z‖*z.im^((k : ℝ)/2) ≤ M) :
    Integrable (fun z => UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed n A) F z) := by
  let r : ℝ := 4*Real.pi*(n : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  let δ := A/r
  have hδ : 0 < δ := div_pos hA hr
  let S := (Ioc (0 : ℝ) 1) ×ˢ (Ioi δ)
  let G := spectralPeterssonStripCoordinates k n F
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hpos : S ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hδ.trans hp.2
  have he := spectralPeterssonCutStrip_coordinates k n A F
  rw [he,upperHalfPlane_integrable_coordinates_smul]
  have hind : (fun p : ℝ × ℝ => (p.2^2)⁻¹ • S.indicator G p) =
      S.indicator (fun p => (p.2^2)⁻¹ • G p) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  rw [hind]
  change Integrable (S.indicator (fun p => (p.2^2)⁻¹ • G p))
    ((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2})
  rw [integrable_indicator_iff hS]
  change Integrable _ (((volume : Measure (ℝ × ℝ)).restrict {p | 0 < p.2}).restrict S)
  rw [Measure.restrict_restrict_of_subset hpos]
  exact spectralPeterssonCutCoordinates_weighted_integrable k hk n δ hδ F hF M hbd

end ArtinMatthews
