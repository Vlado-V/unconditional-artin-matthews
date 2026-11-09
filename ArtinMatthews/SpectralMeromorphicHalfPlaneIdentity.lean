module

public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Tactic.NormNum


set_option backward.privateInPublic true
@[expose] public section

/-! A meromorphic identity known on the initial half-plane propagates as
an equality of genuine punctured germs throughout the parameter plane. -/

noncomputable section
open Set Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralMeromorphic_zero_germ_of_initial_halfPlane (f : ℂ → ℂ)
    (hf : Meromorphic f) (hz : ∀ s : ℂ, 1 < s.re → f s = 0) (s : ℂ) :
    ∀ᶠ w in 𝓝[≠] s, f w = 0 := by
  have hnear : ∀ᶠ w in 𝓝 (2 : ℂ), 1 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hzero : ∀ᶠ w in 𝓝[≠] (2 : ℂ), f w = 0 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with w hw
    exact hz w hw
  have horder : meromorphicOrderAt f (2 : ℂ) = ⊤ := meromorphicOrderAt_eq_top_iff.mpr hzero
  have hm : MeromorphicOn f univ := fun w _ => hf w
  exact meromorphicOrderAt_eq_top_iff.mp
    (hm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (mem_univ (2 : ℂ)) (mem_univ s) horder)

end ArtinMatthews
