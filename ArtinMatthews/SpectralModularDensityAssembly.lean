module

public import ArtinMatthews.SpectralModularDensityCharts


set_option backward.privateInPublic true
@[expose] public section

/-! Finite-chart assembly of smooth-core density.  The one-chart approximation
input is isolated here; the final specialization will supply it by actual
supported smooth approximation, rather than a density postulate. -/

noncomputable section
open Set MeasureTheory
open scoped CompactlySupported MatrixGroups

namespace ArtinMatthews

attribute [local instance] Classical.propDecidable

private theorem chart_single_continuous (N : ℕ) [NeZero N]
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Continuous (fun f : Lp ℂ 2 (volume.restrict ModularGroup.fd) =>
      (PiLp.single 2 q f : Gamma0RegionL2 N)) := by
  have hi : Isometry (fun f : Lp ℂ 2 (volume.restrict ModularGroup.fd) =>
      (PiLp.single 2 q f : Gamma0RegionL2 N)) :=
    Isometry.of_dist_eq fun f g => PiLp.dist_single_same 2
      (fun _ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
        Lp ℂ 2 (volume.restrict ModularGroup.fd)) q f g
  exact hi.continuous

/-- Independence of the actual interior periodizations upgrades supported
smooth density in one chart to the full finite chart Hilbert space. -/
theorem gamma0CompactCoreL2_eq_top_of_smooth_interior_dense (N : ℕ) [NeZero N]
    (hd : Dense {f : Lp ℂ 2 (volume.restrict ModularGroup.fd) |
      ∃ ψ : h2SmoothCompactSeeds, tsupport ψ.val ⊆ ModularGroup.fdo ∧
        f =ᵐ[volume.restrict ModularGroup.fd] ψ.val}) :
    gamma0CompactCoreL2 N = ⊤ := by
  have hsingle (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
      (f : Lp ℂ 2 (volume.restrict ModularGroup.fd)) :
      PiLp.single 2 q f ∈ gamma0CompactCoreL2 N := by
    have hclosed : IsClosed {g : Lp ℂ 2 (volume.restrict ModularGroup.fd) |
        PiLp.single 2 q g ∈ gamma0CompactCoreL2 N} :=
      (Submodule.isClosed_topologicalClosure _).preimage (chart_single_continuous N q)
    exact hd.induction (fun g ⟨ψ, hψ, hgeq⟩ =>
      gamma0CompactCoreL2_contains_single_smooth_interior N q ψ hψ g hgeq) hclosed f
  apply Submodule.eq_top_iff'.mpr
  intro f
  have heq : f = ∑ q, PiLp.single 2 q (f q) := by
    apply PiLp.ext
    intro t
    change f t = (∑ q, PiLp.single 2 q (f q)) t
    have hsum := WithLp.ofLp_sum 2 _ Finset.univ
      (fun q => (PiLp.single 2 q (f q) : Gamma0RegionL2 N))
    have ht := congrArg (fun g => g t) hsum
    rw [ht]
    simp
  rw [heq]
  exact (gamma0CompactCoreL2 N).sum_mem fun q _ => hsingle q (f q)

theorem gamma0SmoothSeedMass_denseRange_of_smooth_interior_dense (N : ℕ) [NeZero N]
    (hd : Dense {f : Lp ℂ 2 (volume.restrict ModularGroup.fd) |
      ∃ ψ : h2SmoothCompactSeeds, tsupport ψ.val ⊆ ModularGroup.fdo ∧
        f =ᵐ[volume.restrict ModularGroup.fd] ψ.val}) :
    DenseRange (gamma0SmoothSeedMass N) := by
  have h := (Submodule.dense_iff_topologicalClosure_eq_top
    (s := (gamma0SmoothSeedMass N).range)).mpr
      (gamma0CompactCoreL2_eq_top_of_smooth_interior_dense N hd)
  exact h

end ArtinMatthews
