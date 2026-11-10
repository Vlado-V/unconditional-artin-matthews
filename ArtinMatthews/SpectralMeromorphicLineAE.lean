module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! Meromorphic germ identities hold almost everywhere on any injectively
parameterized real line. Only the countable singular set is excluded. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace ArtinMatthews

theorem spectralMeromorphic_zero_ae_of_zero_germs (f : ℂ → ℂ) (hf : Meromorphic f)
    (hz : ∀ s : ℂ, ∀ᶠ z in 𝓝[≠] s, f z = 0) (L : ℝ → ℂ) (hL : Function.Injective L) :
    ∀ᵐ t ∂(volume : Measure ℝ), f (L t) = 0 := by
  have hc : (L ⁻¹' {s | AnalyticAt ℂ f s}ᶜ).Countable := hf.countable_compl_analyticAt.preimage hL
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), AnalyticAt ℂ f (L t) := ae_iff.mpr (hc.measure_zero volume)
  filter_upwards [hae] with t ht
  have hv : Tendsto f (𝓝[≠] (L t)) (𝓝 (f (L t))) :=
    ht.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto f (𝓝[≠] (L t)) (𝓝 0) :=
    (tendsto_congr' (hz (L t))).mpr tendsto_const_nhds
  exact tendsto_nhds_unique hv hzero

end ArtinMatthews
