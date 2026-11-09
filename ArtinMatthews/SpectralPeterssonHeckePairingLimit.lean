module

public import ArtinMatthews.SpectralPeterssonHeckeReproduce
public import ArtinMatthews.SpectralPeterssonWeightedBound
public import ArtinMatthews.SpectralHyperbolicFiniteVolume
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Passing the regulated pairing to its actual weight-two limit on
the finite-volume Gamma0 region. -/

noncomputable section
open Filter Set MeasureTheory Matrix UpperHalfPlane
open scoped MatrixGroups Topology ENNReal ComplexConjugate

namespace ArtinMatthews

theorem gamma0InteriorRegion_volume_lt_top (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (gamma0InteriorRegion N) < ∞ := by
  classical
  let _ : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
  have hf : (volume : Measure UpperHalfPlane) ModularGroup.fdo < ∞ :=
    (measure_mono ModularGroup.fdo_subset_fd).trans_lt modular_fundamental_region_volume_lt_top
  have hc (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      (volume : Measure UpperHalfPlane) (gamma0InteriorChart N q) = volume ModularGroup.fdo :=
    (h2_integer_measurePreserving q.out).measure_preimage ModularGroup.isOpen_fdo.measurableSet.nullMeasurableSet
  unfold gamma0InteriorRegion
  refine (measure_iUnion_le _).trans_lt ?_
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr (fun q _ => (hc q).symm ▸ hf)

theorem gamma0PeterssonHecke_measurable (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (u : ℝ) (n : ℕ+) : Measurable (gamma0PeterssonHecke N a u n) := by
  let _ : Countable (Gamma0PeterssonSignedRow N 1 a) :=
    (show Function.Injective (fun p : Gamma0PeterssonSignedRow N 1 a => p.val) from
      Subtype.val_injective).countable
  have h (p : Gamma0PeterssonSignedRow N 1 a) : Continuous (gamma0PeterssonHeckeSignedSummand N 1 a u n p) := by
    unfold gamma0PeterssonHeckeSignedSummand gamma0PeterssonHeckeMatrixSeed
    exact spectralHolomorphicSlash_continuous 2 _ _ (spectralPeterssonHeckeSeed_continuous u n)
  unfold gamma0PeterssonHecke gamma0PeterssonHeckeChart
  exact measurable_const.mul (Measurable.tsum fun p => (h p).measurable)

private theorem peterssonTwo_norm (P F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖UpperHalfPlane.petersson 2 P F z‖ = (‖P z‖*z.im)*(‖F z‖*z.im) := by
  unfold UpperHalfPlane.petersson
  simp only [norm_mul,Complex.norm_conj]
  change ‖P z‖*‖F z‖*‖(z.im : ℂ)^(2 : ℕ)‖ = _
  rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg z.im_pos.le]
  ring

theorem gamma0PeterssonInner_hecke_tendsto (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (n : ℕ+) (F P : UpperHalfPlane → ℂ) (hF : Continuous F) (M C : ℝ)
    (hFbd : ∀ z ∈ gamma0InteriorRegion N, ‖F z‖*z.im ≤ M)
    (hPbd : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ z ∈ gamma0InteriorRegion N,
      ‖gamma0PeterssonHecke N a u n z‖*z.im ≤ C)
    (hlim : ∀ z ∈ gamma0InteriorRegion N,
      Tendsto (fun u : ℝ => gamma0PeterssonHecke N a u n z) (𝓝[>] 0) (𝓝 (P z))) :
    IntegrableOn (UpperHalfPlane.petersson 2 P F) (gamma0InteriorRegion N) ∧
      Tendsto (fun u : ℝ => gamma0PeterssonInner N 2 (gamma0PeterssonHecke N a u n) F)
        (𝓝[>] 0) (𝓝 (gamma0PeterssonInner N 2 P F)) := by
  let S := gamma0InteriorRegion N
  let μ := volume.restrict S
  let L := 𝓝[>] (0 : ℝ)
  let G (u : ℝ) := UpperHalfPlane.petersson 2 (gamma0PeterssonHecke N a u n) F
  let H := UpperHalfPlane.petersson 2 P F
  let D := max C 0 * max M 0
  have hS : MeasurableSet S := (gamma0InteriorRegion_isOpen N).measurableSet
  let _ : IsFiniteMeasure μ := ⟨by
    rw [show μ = volume.restrict S from rfl,Measure.restrict_apply_univ]
    exact gamma0InteriorRegion_volume_lt_top N⟩
  have hpow : Measurable (fun z : UpperHalfPlane => (z.im : ℂ)^(2 : ℤ)) := by
    change Measurable (fun z : UpperHalfPlane => (z.im : ℂ)^(2 : ℕ))
    exact ((Complex.continuous_ofReal.comp continuous_im).pow 2).measurable
  have hG (u : ℝ) : AEStronglyMeasurable (G u) μ := by
    unfold G UpperHalfPlane.petersson
    have hc := (continuous_star : Continuous (star : ℂ → ℂ)).measurable.comp
      (gamma0PeterssonHecke_measurable N a u n)
    exact ((hc.mul hF.measurable).mul hpow).aestronglyMeasurable
  have hnear : ∀ᶠ u : ℝ in L, u ∈ Ioc (0 : ℝ) 1 := by
    have hlt : ∀ᶠ u : ℝ in L, u < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    have hpos : ∀ᶠ u : ℝ in L, 0 < u := self_mem_nhdsWithin
    filter_upwards [hpos,hlt] with u hu hu'
    exact ⟨hu,hu'.le⟩
  have hb (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) (z : UpperHalfPlane) (hz : z ∈ S) : ‖G u z‖ ≤ D := by
    unfold G D
    rw [peterssonTwo_norm]
    exact mul_le_mul ((hPbd u hu z hz).trans (le_max_left _ _))
      ((hFbd z hz).trans (le_max_left _ _)) (mul_nonneg (norm_nonneg _) z.im_pos.le) (le_max_right _ _)
  have hlim' (z : UpperHalfPlane) (hz : z ∈ S) : Tendsto (fun u => G u z) L (𝓝 (H z)) := by
    unfold G H UpperHalfPlane.petersson
    have hc := ((continuous_star : Continuous (star : ℂ → ℂ)).tendsto (P z)).comp (hlim z hz)
    exact (hc.mul tendsto_const_nhds).mul tendsto_const_nhds
  have hlimAE : ∀ᵐ z ∂μ, Tendsto (fun u => G u z) L (𝓝 (H z)) :=
    (ae_restrict_mem hS).mono hlim'
  have hD : Integrable (fun _ : UpperHalfPlane => D) μ := integrable_const _
  have hlimBound : ∀ᵐ z ∂μ, ‖H z‖ ≤ D := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact le_of_tendsto (hlim' z hz).norm (hnear.mono (fun u hu => hb u hu z hz))
  refine ⟨hD.mono' (aestronglyMeasurable_of_tendsto_ae L hG hlimAE) hlimBound,?_⟩
  change Tendsto (fun u => ∫ z, G u z ∂μ) L (𝓝 (∫ z, H z ∂μ))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => D) (Eventually.of_forall hG) _ hD hlimAE
  apply hnear.mono
  intro u hu
  exact (ae_restrict_mem hS).mono (fun z hz => hb u hu z hz)

theorem spectralPeterssonHeckeMass_zero (n : ℕ+) :
    spectralPeterssonHeckeMass 0 n = spectralPeterssonReproducingMass 2 n := by
  norm_num [spectralPeterssonHeckeMass,spectralPeterssonReproducingMass,Real.Gamma_one,Real.rpow_one]

theorem spectralPeterssonHeckeMass_tendsto (n : ℕ+) :
    Tendsto (fun u : ℝ => spectralPeterssonHeckeMass u n) (𝓝[>] 0)
      (𝓝 (spectralPeterssonReproducingMass 2 n)) := by
  let r := 4*Real.pi*(n : ℝ)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hg : ContinuousAt (fun u : ℝ => Real.Gamma (1+u)) 0 := by
    have h := (Real.hasDerivAt_Gamma_of_pos (by norm_num : 0 < (1 : ℝ))).continuousAt
    exact (show ContinuousAt Real.Gamma (1+(0 : ℝ)) by simpa only [add_zero] using h).comp (by fun_prop)
  have hd : ContinuousAt (fun u : ℝ => r^(1+u)) 0 :=
    ((Real.continuous_const_rpow hr.ne').comp (continuous_const.add continuous_id)).continuousAt
  have h : ContinuousAt (fun u : ℝ => spectralPeterssonHeckeMass u n) 0 :=
    hg.div hd (Real.rpow_pos_of_pos hr _).ne'
  simpa only [spectralPeterssonHeckeMass_zero] using h.tendsto.mono_left nhdsWithin_le_nhds

theorem gamma0PeterssonInner_hecke_limit_reproduce (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (n : ℕ+) (F P : UpperHalfPlane → ℂ) (hCont : Continuous F)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, spectralHolomorphicSlash 2 (atkinRealMap γ.val) F = F)
    (M C : ℝ) (hbd : ∀ z, ‖spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N a) F z‖*z.im ≤ M)
    (hPbd : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ z ∈ gamma0InteriorRegion N,
      ‖gamma0PeterssonHecke N a u n z‖*z.im ≤ C)
    (hlim : ∀ z ∈ gamma0InteriorRegion N,
      Tendsto (fun u : ℝ => gamma0PeterssonHecke N a u n z) (𝓝[>] 0) (𝓝 (P z)))
    (A : ℂ) (hA : ∀ (y : ℝ) (hy : 0 < y), spectralPeterssonFourierAtHeight
      (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N a) F) n y hy = A) :
    gamma0PeterssonInner N 2 P F = (spectralPeterssonReproducingMass 2 n : ℂ)*A := by
  let σ := gamma0TrueCuspScaling N a
  have hCont' : Continuous (spectralHolomorphicSlash 2 σ F) := spectralHolomorphicSlash_continuous 2 σ F hCont
  have hFbd (z : UpperHalfPlane) : ‖F z‖*z.im ≤ M := by
    have he := spectralPeterssonWeightedNorm_slash 2 σ F (σ⁻¹ • z)
    rw [smul_inv_smul] at he
    have h := hbd (σ⁻¹ • z)
    norm_num [spectralPeterssonWeightedNorm,Real.rpow_one] at he
    exact he ▸ h
  have hI := (gamma0PeterssonInner_hecke_tendsto N a n F P hCont M C (fun z _ => hFbd z) hPbd hlim).2
  have he : (fun u : ℝ => gamma0PeterssonInner N 2 (gamma0PeterssonHecke N a u n) F) =ᶠ[𝓝[>] 0]
      fun u => (spectralPeterssonHeckeMass u n : ℂ)*A := by
    filter_upwards [show ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u from self_mem_nhdsWithin] with u hu
    exact gamma0PeterssonInner_hecke_reproduce N a u hu n F hF hCont' M hbd A hA
  have hMass := ((Complex.continuous_ofReal.tendsto _).comp (spectralPeterssonHeckeMass_tendsto n)).mul_const A
  exact tendsto_nhds_unique hI (hMass.congr' he.symm)

end ArtinMatthews
