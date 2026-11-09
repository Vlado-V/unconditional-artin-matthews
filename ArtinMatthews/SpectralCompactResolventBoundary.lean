module

public import ArtinMatthews.SpectralStoneParameterLift
public import ArtinMatthews.SpectralCompactResolventCriticalJump


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual scalar ambient resolvents converge to the matching
values at every corresponding regular upper and lower boundary point. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0CompactForcingDiagonalTest (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (Y : Gamma0CompactResolventCutoff N ψ) (s : ℂ) : ℂ :=
  gamma0CompactForcingResolventMeromorphicTest N ψ ψ Y s

theorem gamma0CompactForcingDiagonalTest_analyticAt_offcut (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    AnalyticAt ℂ (gamma0CompactForcingDiagonalTest N ψ Y) s := by
  let F := gamma0SmoothSeedMass N ψ
  let A (w : ℂ) := gamma0AmbientResolventFamily N (w*(1-w))
  have ha : AnalyticAt ℂ A s := (gamma0AmbientResolventFamily_analyticAt N (s*(1-s)) hs.2).comp
    (f:=fun w : ℂ => w*(1-w)) (analyticAt_id.mul (analyticAt_const.sub analyticAt_id))
  have h : AnalyticAt ℂ (fun w : ℂ => inner ℂ F (A w F)) s :=
    ((innerSL ℂ F).analyticAt (A s F)).comp (f:=fun w : ℂ => A w F)
      (spectralAnalytic_clmApply A (fun _ => F) s ha analyticAt_const)
  apply h.congr
  filter_upwards [gamma0EisensteinContinuationDomain_open.mem_nhds hs] with w hw
  exact (gamma0CompactForcingResolventMeromorphicTest_offcut N ψ ψ Y w hw).symm

theorem gamma0CompactForcingDiagonalTest_analyticAt_regular (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ)
    (s : ℂ) (hs : gamma0HeightMatchingRegular N Y.height Y.pos s) :
    AnalyticAt ℂ (gamma0CompactForcingDiagonalTest N ψ Y) s :=
  gamma0CompactForcingResolventMeromorphicTest_analyticAt_regular N ψ ψ Y s hs

theorem gamma0CompactForcingStone_upper_tendsto (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ)
    (hx : gamma0HeightMatchingRegular N Y.height Y.pos (spectralStoneUpperParameter x 0)) :
    Tendsto (fun ε : ℝ => inner ℂ (gamma0SmoothSeedMass N ψ)
      (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) (gamma0SmoothSeedMass N ψ)))
      (𝓝[>] (0:ℝ)) (𝓝 (gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneUpperParameter x 0))) := by
  have hPair : Continuous (fun ε : ℝ => (x,ε)) := continuous_const.prodMk continuous_id
  have hc : Continuous (fun ε : ℝ => spectralStoneUpperParameter x ε) :=
    spectralStoneUpperParameter_continuous.comp (f:=fun ε : ℝ => (x,ε)) hPair
  have hp : Tendsto (fun ε : ℝ => spectralStoneUpperParameter x ε) (𝓝[>] (0:ℝ))
      (𝓝 (spectralStoneUpperParameter x 0)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (gamma0CompactForcingDiagonalTest_analyticAt_regular N ψ Y _ hx).continuousAt.tendsto.comp hp
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  let sε := spectralStoneUpperParameter x ε
  let F := gamma0SmoothSeedMass N ψ
  have ho := gamma0CompactForcingResolventMeromorphicTest_offcut N ψ ψ Y sε
    (spectralStoneUpperParameter_domain x ε hε)
  have hEnergy : sε*(1-sε)=spectralEnergyShift x ε :=
    spectralStoneUpperParameter_energy x ε hε.le
  change gamma0CompactForcingDiagonalTest N ψ Y sε=
    inner ℂ F (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) F)
  exact ho.trans (congrArg (fun z : ℂ => inner ℂ F (gamma0AmbientResolventFamily N z F)) hEnergy)

theorem gamma0CompactForcingStone_lower_tendsto (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ)
    (hx : gamma0HeightMatchingRegular N Y.height Y.pos (spectralStoneLowerParameter x 0)) :
    Tendsto (fun ε : ℝ => inner ℂ (gamma0SmoothSeedMass N ψ)
      (gamma0AmbientResolventFamily N (spectralEnergyShift x (-ε)) (gamma0SmoothSeedMass N ψ)))
      (𝓝[>] (0:ℝ)) (𝓝 (gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneLowerParameter x 0))) := by
  have hPair : Continuous (fun ε : ℝ => (x,ε)) := continuous_const.prodMk continuous_id
  have hc : Continuous (fun ε : ℝ => spectralStoneLowerParameter x ε) :=
    spectralStoneLowerParameter_continuous.comp (f:=fun ε : ℝ => (x,ε)) hPair
  have hp : Tendsto (fun ε : ℝ => spectralStoneLowerParameter x ε) (𝓝[>] (0:ℝ))
      (𝓝 (spectralStoneLowerParameter x 0)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (gamma0CompactForcingDiagonalTest_analyticAt_regular N ψ Y _ hx).continuousAt.tendsto.comp hp
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  let sε := spectralStoneLowerParameter x ε
  let F := gamma0SmoothSeedMass N ψ
  have ho := gamma0CompactForcingResolventMeromorphicTest_offcut N ψ ψ Y sε
    (spectralStoneLowerParameter_domain x ε hε)
  have hEnergy : sε*(1-sε)=spectralEnergyShift x (-ε) :=
    spectralStoneLowerParameter_energy x ε hε.le
  change gamma0CompactForcingDiagonalTest N ψ Y sε=
    inner ℂ F (gamma0AmbientResolventFamily N (spectralEnergyShift x (-ε)) F)
  exact ho.trans (congrArg (fun z : ℂ => inner ℂ F (gamma0AmbientResolventFamily N z F)) hEnergy)

theorem gamma0CompactForcingStone_boundary_conj (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (Y : Gamma0CompactResolventCutoff N ψ) (x : ℝ)
    (hu : gamma0HeightMatchingRegular N Y.height Y.pos (spectralStoneUpperParameter x 0))
    (hl : gamma0HeightMatchingRegular N Y.height Y.pos (spectralStoneLowerParameter x 0)) :
    (starRingEnd ℂ) (gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneLowerParameter x 0))=
      gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneUpperParameter x 0) := by
  let F := gamma0SmoothSeedMass N ψ
  have h := Complex.continuous_conj.continuousAt.tendsto.comp
    (gamma0CompactForcingStone_lower_tendsto N ψ Y x hl)
  have h' : Tendsto (fun ε : ℝ => inner ℂ F (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) F))
      (𝓝[>] (0:ℝ))
      (𝓝 ((starRingEnd ℂ) (gamma0CompactForcingDiagonalTest N ψ Y (spectralStoneLowerParameter x 0)))) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0<ε at hε
    change (starRingEnd ℂ) (inner ℂ F (gamma0AmbientResolventFamily N (spectralEnergyShift x (-ε)) F))=
      inner ℂ F (gamma0AmbientResolventFamily N (spectralEnergyShift x ε) F)
    rw [gamma0AmbientResolventFamily_diagonal_conj N _ (spectralEnergyShift_offcut x _ (neg_ne_zero.mpr hε.ne')),
      spectralEnergyShift_conj,neg_neg]
  exact tendsto_nhds_unique h' (gamma0CompactForcingStone_upper_tendsto N ψ Y x hu)

end ArtinMatthews
