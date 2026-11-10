module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! A nonzero value of an entire function gives a nonzero punctured germ
at every parameter. This supplies division for the actual compact probe. -/

noncomputable section
open Set Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralAnalytic_nonzero_germ_of_value (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (z₀ : ℂ) (h₀ : f z₀ ≠ 0) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, f z ≠ 0 := by
  have hm : MeromorphicOn f univ := fun z hz => (hf z hz).meromorphicAt
  have ho : meromorphicOrderAt f z₀ ≠ ⊤ := by
    intro h
    have hzero := meromorphicOrderAt_eq_top_iff.mp h
    have heq := hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (mem_univ z₀) hzero.frequently
    exact h₀ (heq (mem_univ z₀))
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm s (mem_univ s))).mp
    (hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ z₀) (mem_univ s) ho)

end ArtinMatthews
