module

public import ArtinMatthews.SpectralStoneBoundaryDensity
public import Mathlib.MeasureTheory.Integral.CompactlySupported


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine scalar spectral measure agrees with the actual boundary
density against every compact test supported inside the regular energies. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped InnerProductSpace CompactlySupported
namespace ArtinMatthews

def gamma0StoneUpperBoundaryBand (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (p : ℝ×ℝ) : ℝ :=
  (gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneUpperParameter p.1 p.2)).im

theorem gamma0StoneUpperBoundaryBand_eq_resolvent (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (x ε : ℝ) (hε : 0<ε) :
    gamma0StoneUpperBoundaryBand N ψ Y (x,ε)=
      (inner ℂ (gamma0SmoothSeedMass N ψ)
        (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) (gamma0SmoothSeedMass N ψ))).im := by
  let F := gamma0SmoothSeedMass N ψ
  let s := spectralStoneUpperParameter x ε
  have h := gamma0CompactForcingResolventMeromorphicTest_offcut N ψ ψ Y s
    (spectralStoneUpperParameter_domain x ε hε)
  have hE : s*(1-s)=spectralEnergyShift x ε := spectralStoneUpperParameter_energy x ε hε.le
  exact congrArg Complex.im (h.trans (congrArg (fun z : ℂ => inner ℂ F (gamma0AmbientResolventFamily N z F)) hE))

theorem gamma0StoneUpperBoundaryBand_continuousAt_of_analytic (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (p : ℝ×ℝ)
    (h : AnalyticAt ℂ (gamma0CompactForcingDiagonalTest N ψ Y) (spectralStoneUpperParameter p.1 p.2)) :
    ContinuousAt (gamma0StoneUpperBoundaryBand N ψ Y) p := by
  have hP : ContinuousAt (fun q : ℝ×ℝ => spectralStoneUpperParameter q.1 q.2) p :=
    spectralStoneUpperParameter_continuous.continuousAt
  have hM : ContinuousAt (fun q : ℝ×ℝ =>
      gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneUpperParameter q.1 q.2)) p :=
    h.continuousAt.comp' (f:=fun q : ℝ×ℝ => spectralStoneUpperParameter q.1 q.2) hP
  exact Complex.continuous_im.continuousAt.comp' hM

theorem gamma0StoneUpperBoundaryBand_continuousOn (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) :
    ContinuousOn (gamma0StoneUpperBoundaryBand N ψ Y)
      (gamma0StoneGoodEnergy N ψ Y ×ˢ Ici (0:ℝ)) := by
  intro p hp
  have ha : AnalyticAt ℂ (gamma0CompactForcingDiagonalTest N ψ Y) (spectralStoneUpperParameter p.1 p.2) := by
    have hp0 : (0:ℝ)≤p.2 := hp.2
    rcases eq_or_lt_of_le hp0 with he | he
    · rw [← he]
      exact gamma0CompactForcingDiagonalTest_analyticAt_regular N ψ Y _ hp.1.2.1
    · exact gamma0CompactForcingDiagonalTest_analyticAt_offcut N ψ Y _
        (spectralStoneUpperParameter_domain p.1 p.2 he)
  exact (gamma0StoneUpperBoundaryBand_continuousAt_of_analytic N ψ Y p ha).continuousWithinAt

theorem gamma0StoneUpperBoundaryBand_horizontal_continuous (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) {ε : ℝ} (hε : 0<ε) :
    Continuous (fun x : ℝ => gamma0StoneUpperBoundaryBand N ψ Y (x,ε)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have ha := gamma0CompactForcingDiagonalTest_analyticAt_offcut N ψ Y _
    (spectralStoneUpperParameter_domain x ε hε)
  have hc : Continuous (fun x : ℝ => (x,ε)) := continuous_id.prodMk continuous_const
  exact (gamma0StoneUpperBoundaryBand_continuousAt_of_analytic N ψ Y (x,ε) ha).comp' (f:=fun x : ℝ => (x,ε)) hc.continuousAt

theorem gamma0AmbientStone_compactTest_density (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (f : C_c(ℝ,ℝ)) (hf : tsupport f⊆gamma0StoneGoodEnergy N ψ Y) :
    (∫ x,f x ∂gamma0AmbientSpectralMeasure N (gamma0SmoothSeedMass N ψ))=
      ∫ x : ℝ,gamma0StoneBoundaryDensity N ψ Y x*f x := by
  let K := tsupport f
  let F := gamma0SmoothSeedMass N ψ
  let B := gamma0StoneUpperBoundaryBand N ψ Y
  let R (ε x : ℝ) := (inner ℂ F (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) F)).im
  have he (x ε : ℝ) (hε : 0<ε) : R ε x=B (x,ε) :=
    (gamma0StoneUpperBoundaryBand_eq_resolvent N ψ Y x ε hε).symm
  have hC : ContinuousOn B (K ×ˢ Icc (0:ℝ) 1) :=
    (gamma0StoneUpperBoundaryBand_continuousOn N ψ Y).mono
      (Set.prod_mono hf (Icc_subset_Ici_self))
  obtain ⟨C,hC⟩ := (f.hasCompactSupport.prod isCompact_Icc).exists_bound_of_continuousOn hC
  have hD : Tendsto (fun ε : ℝ => ∫ x : ℝ,R ε x*f x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x : ℝ,B (x,0)*f x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => max C 0*‖f x‖)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hp : 0<ε := hε
      have h : (fun x : ℝ => R ε x*f x)=(fun x : ℝ => B (x,ε)*f x) :=
        funext (fun x => congrArg (fun r : ℝ => r*f x) (he x ε hp))
      rw [h]
      exact ((gamma0StoneUpperBoundaryBand_horizontal_continuous N ψ Y hp).mul f.continuous).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))] with ε hε hε₁
      have hp : 0<ε := hε
      exact Eventually.of_forall fun x => by
        change ‖R ε x*f x‖ ≤ max C 0*‖f x‖
        by_cases hx : x∈K
        · rw [he x ε hp,norm_mul]
          exact mul_le_mul_of_nonneg_right
            ((hC (x,ε) ⟨hx,⟨hp.le,hε₁.le⟩⟩).trans (le_max_left _ _)) (norm_nonneg _)
        · have hz : f x=0 := image_eq_zero_of_notMem_tsupport hx
          simp [hz]
    · exact f.integrable.norm.const_mul _
    · exact Eventually.of_forall fun x => by
        by_cases hx : x∈K
        · have ht := gamma0CompactForcingStone_upper_tendsto N ψ Y x (hf hx).2.1
          have hi : Tendsto (fun ε => R ε x) (𝓝[>] (0:ℝ)) (𝓝 (B (x,0))) :=
            Complex.continuous_im.continuousAt.tendsto.comp ht
          exact hi.mul_const (f x)
        · have h0 : f x=0 := image_eq_zero_of_notMem_tsupport hx
          simpa only [h0,mul_zero] using (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => (0:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0))
  have hNorm : Real.pi⁻¹*(∫ x : ℝ,B (x,0)*f x)=
      ∫ x : ℝ,gamma0StoneBoundaryDensity N ψ Y x*f x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change Real.pi⁻¹*(B (x,0)*f x)=(B (x,0)/Real.pi)*f x
      ring
  have hlim := tendsto_const_nhds.mul hD (a:=Real.pi⁻¹)
  rw [hNorm] at hlim
  exact tendsto_nhds_unique (gamma0AmbientSpectralMeasure_stone N F f) hlim

end ArtinMatthews
