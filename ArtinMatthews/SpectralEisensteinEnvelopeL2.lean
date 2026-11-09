module

public import ArtinMatthews.SpectralEisensteinRemainderSeries
public import ArtinMatthews.SpectralEisensteinRadialEnvelope


set_option backward.privateInPublic true
@[expose] public section

/-! The global positive envelope is genuinely in ambient L². It is the
actual real-parameter remainder plus a compact smooth height profile. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem cuspEisensteinNormalizedHeight_rpow_summable (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (σ : ℝ) (hσ : 1 < σ) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a =>
      (cuspEisensteinNormalizedHeight N r a v z)^σ) := by
  have h := cuspEisensteinNormalizedHeight_power_summable_norm N r a (σ:ℂ) hσ z
  convert h using 1
  funext v
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (cuspEisensteinNormalizedHeight_pos N r a v z) (σ:ℂ)).symm

theorem cuspEisensteinRadialEnvelope_summable (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (σ : ℝ) (hσ : 1 < σ) (z : UpperHalfPlane) :
    Summable (fun v : Gamma0CuspEisensteinRows N r a =>
      eisensteinRadialEnvelope σ (cuspEisensteinNormalizedHeight N r a v z)) := by
  apply (cuspEisensteinNormalizedHeight_rpow_summable N r a σ hσ z).of_nonneg_of_le
    (fun v => eisensteinRadialEnvelope_nonneg σ (cuspEisensteinNormalizedHeight_pos N r a v z))
  intro v
  unfold eisensteinRadialEnvelope
  apply mul_le_of_le_one_left (Real.rpow_nonneg (cuspEisensteinNormalizedHeight_pos N r a v z).le _)
  linarith [(eisensteinHeightCutoff_range (cuspEisensteinNormalizedHeight N r a v z/2)).1]

def gamma0CuspRadialEnvelope (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (σ : ℝ)
    (z : UpperHalfPlane) : ℝ :=
  (1/2:ℝ)*∑' v : Gamma0CuspEisensteinRows N 1 a,
    eisensteinRadialEnvelope σ (cuspEisensteinNormalizedHeight N 1 a v z)

theorem gamma0CuspRadialEnvelope_nonneg (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (σ : ℝ)
    (z : UpperHalfPlane) : 0 ≤ gamma0CuspRadialEnvelope N a σ z :=
  mul_nonneg (by norm_num) (tsum_nonneg (fun v =>
    eisensteinRadialEnvelope_nonneg σ (cuspEisensteinNormalizedHeight_pos N 1 a v z)))

theorem gamma0CuspRadialEnvelope_eq (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (σ : ℝ) (hσ : 1 < σ) (z : UpperHalfPlane) :
    (gamma0CuspRadialEnvelope N a σ z:ℂ)=
      gamma0CuspEisensteinRemainder N a (σ:ℂ) z+
        gamma0CuspHeightProfile N a (eisensteinEnvelopeCorrection (σ:ℂ)) z := by
  have hR := (cuspEisensteinRemainderProfile_summable_norm N 1 a (σ:ℂ) hσ z).of_norm
  have hC : Summable (fun v : Gamma0CuspEisensteinRows N 1 a =>
      eisensteinEnvelopeCorrection (σ:ℂ) (cuspEisensteinNormalizedHeight N 1 a v z)) :=
    summable_of_hasFiniteSupport (cuspEisensteinProfile_hasFiniteSupport N 1 a _
      (by norm_num : (0:ℝ)<1) (fun t ht => eisensteinEnvelopeCorrection_zero_low _ ht) z)
  rw [gamma0CuspRadialEnvelope,Complex.ofReal_mul,Complex.ofReal_tsum]
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  simp_rw [eisensteinRadialEnvelope_decomposition σ (cuspEisensteinNormalizedHeight_pos N 1 a _ z)]
  rw [hR.tsum_add hC,mul_add,← gamma0CuspEisensteinRemainder_eq_tsum N a (σ:ℂ) hσ z,
    ← gamma0CuspHeightProfile_eq_tsum N a _ (by norm_num : (0:ℝ)<1)
      (fun t ht => eisensteinEnvelopeCorrection_zero_low _ ht) z]

theorem gamma0CuspCompactProfile_memLp (N : ℕ) [NeZero N] (a r : SL(2,ℤ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0:ℝ)) :
    MemLp (fun z : UpperHalfPlane => gamma0CuspHeightProfile N a f (r⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) := by
  let ψ := cuspHeightProfileSeed N a f hf hcf hpos
  have h := (gamma0PoincareSeed_memLp_modularRegion N ψ.val r⁻¹).const_mul (1/2:ℂ)
  apply (memLp_congr_ae ?_).mp h
  filter_upwards [] with z
  exact (gamma0CuspHeightProfile_eq_poincare N a f hf hcf hpos (r⁻¹ • z)).symm

theorem gamma0CuspRadialEnvelope_memLp (N : ℕ) [NeZero N] (a r : SL(2,ℤ))
    (σ : ℝ) (hσ : 1 < σ) :
    MemLp (fun z : UpperHalfPlane => gamma0CuspRadialEnvelope N a σ (r⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) := by
  have hR := gamma0CuspEisensteinRemainder_memLp_modularRegion N a (σ:ℂ) hσ r
  have hC := gamma0CuspCompactProfile_memLp N a r (eisensteinEnvelopeCorrection (σ:ℂ))
    (eisensteinEnvelopeCorrection_smooth _) (eisensteinEnvelopeCorrection_compact _)
    (eisensteinEnvelopeCorrection_positive_support _)
  have h : MemLp (fun z : UpperHalfPlane =>
      (gamma0CuspRadialEnvelope N a σ (r⁻¹ • z):ℂ)) 2 (volume.restrict ModularGroup.fd) := by
    apply (memLp_congr_ae ?_).mp (hR.add hC)
    exact Filter.Eventually.of_forall (fun z => (gamma0CuspRadialEnvelope_eq N a σ hσ _).symm)
  apply (memLp_congr_ae ?_).mp h.norm
  filter_upwards [] with z
  simp only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (gamma0CuspRadialEnvelope_nonneg N a σ _)]

theorem gamma0CuspRadialApprox_norm_le (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) {A : ℝ} (hA : 0 < A) (z : UpperHalfPlane) :
    ‖gamma0CuspHeightProfile N a (eisensteinRadialApprox s A) z‖ ≤
      gamma0CuspRadialEnvelope N a s.re z := by
  have hsum := cuspEisensteinRadialEnvelope_summable N 1 a s.re hs z
  have hn : Summable (fun v : Gamma0CuspEisensteinRows N 1 a =>
      ‖eisensteinRadialApprox s A (cuspEisensteinNormalizedHeight N 1 a v z)‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun v => eisensteinRadialApprox_norm_envelope s A (cuspEisensteinNormalizedHeight_pos N 1 a v z))
  rw [gamma0CuspHeightProfile_eq_tsum N a _ (one_div_pos.mpr hA)
    (fun t ht => eisensteinRadialApprox_small_zero s hA ht) z,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum
    (fun v => eisensteinRadialApprox_norm_envelope s A (cuspEisensteinNormalizedHeight_pos N 1 a v z)) hsum)

end ArtinMatthews
