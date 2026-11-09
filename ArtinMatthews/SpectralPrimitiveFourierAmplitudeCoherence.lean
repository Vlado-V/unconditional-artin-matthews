module

public import ArtinMatthews.SpectralPrimitiveFourierAmplitude


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar meromorphic Fourier amplitude is independent, as a germ,
of the auxiliary cusp-height cutoff and its chosen nonzero compact probe. -/

noncomputable section
open Set Filter
open scoped MatrixGroups Topology

namespace ArtinMatthews

theorem gamma0PrimitiveFourierAmplitude_height_coherence (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (n : ℤ) (hn : n ≠ 0) (s : ℂ) :
    gamma0PrimitiveFourierAmplitude N a r Y hY n hn =ᶠ[𝓝[≠] s]
      gamma0PrimitiveFourierAmplitude N a r Z hZ n hn := by
  let D (z : ℂ) := gamma0PrimitiveFourierAmplitude N a r Y hY n hn z-
    gamma0PrimitiveFourierAmplitude N a r Z hZ n hn z
  have hm : MeromorphicOn D univ := fun z _ =>
    (gamma0PrimitiveFourierAmplitude_meromorphic N a r Y hY n hn z).sub
      (gamma0PrimitiveFourierAmplitude_meromorphic N a r Z hZ n hn z)
  have hz : ∀ᶠ z in 𝓝[≠] (2 : ℂ), D z = 0 := by
    filter_upwards [gamma0PrimitiveFourierAmplitude_initial_germ N a r Y hY n hn (2 : ℂ) (by norm_num),
      gamma0PrimitiveFourierAmplitude_initial_germ N a r Z hZ n hn (2 : ℂ) (by norm_num)] with z hy hz
    dsimp only [D]
    rw [hy,hz,sub_self]
  have horder := hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ s) (meromorphicOrderAt_eq_top_iff.mpr hz)
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp horder] with z hz
  exact sub_eq_zero.mp hz

end ArtinMatthews
