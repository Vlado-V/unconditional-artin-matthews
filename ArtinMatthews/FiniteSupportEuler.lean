module

public import ArtinMatthews.FiniteSupportEulerPrefix
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Order.Filter.AtTopBot.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Euler product of a finite-support choice expansion.
Absolute convergence of the original series implies convergence of the
finite-prime prefixes and hence the Euler product, including its zero
choice. No Euler-product identity is a premise. -/

namespace ArtinMatthews.SourceEuler

open Filter
open scoped BigOperators Classical Topology
noncomputable section

variable {P X : Type} [Zero X]

theorem finiteChoice_prefix_indicator (f : P → X → ℂ) (hf : ∀ p, f p 0 = 1)
    (hs : Summable (fun a : P →₀ X => ‖finiteChoiceWeight f a‖)) (S : Finset P) :
    (∏ p ∈ S, ∑' x : X, f p x) =
      ∑' a : P →₀ X, if a.support ⊆ S then finiteChoiceWeight f a else 0 := by
  classical
  rw [← finiteChoice_prefix_sum f hf hs S]
  let s : Set (P →₀ X) := {a | a.support ⊆ S}
  calc
    _ = ∑' a : s, finiteChoiceWeight f a := rfl
    _ = ∑' a : P →₀ X, s.indicator (finiteChoiceWeight f) a :=
      tsum_subtype s (finiteChoiceWeight f)
    _ = _ := by
      apply tsum_congr
      intro a
      simp only [s, Set.indicator_apply, Set.mem_ofPred_eq]

theorem finiteChoice_hasProd (f : P → X → ℂ) (hf : ∀ p, f p 0 = 1)
    (hs : Summable (fun a : P →₀ X => ‖finiteChoiceWeight f a‖)) :
    HasProd (fun p => ∑' x : X, f p x) (∑' a : P →₀ X, finiteChoiceWeight f a) := by
  classical
  have hp (a : P →₀ X) :
      Tendsto (fun S : Finset P => if a.support ⊆ S then finiteChoiceWeight f a else 0)
        atTop (𝓝 (finiteChoiceWeight f a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop a.support] with S hS
    simp only [ite_eq_left hS]
  have hb : ∀ᶠ S : Finset P in atTop, ∀ a : P →₀ X,
      ‖if a.support ⊆ S then finiteChoiceWeight f a else 0‖ ≤ ‖finiteChoiceWeight f a‖ := by
    apply Filter.Eventually.of_forall
    intro S a
    split_ifs
    · exact le_rfl
    · simp only [norm_zero, norm_nonneg]
  have h := tendsto_tsum_of_dominated_convergence hs hp hb
  change Tendsto (fun S : Finset P => ∏ p ∈ S, ∑' x : X, f p x) atTop
    (𝓝 (∑' a : P →₀ X, finiteChoiceWeight f a))
  simpa only [← finiteChoice_prefix_indicator f hf hs] using h

theorem finiteChoice_euler (f : P → X → ℂ) (hf : ∀ p, f p 0 = 1)
    (hs : Summable (fun a : P →₀ X => ‖finiteChoiceWeight f a‖)) :
    (∑' a : P →₀ X, finiteChoiceWeight f a) = ∏' p, ∑' x : X, f p x :=
  (finiteChoice_hasProd f hf hs).tprod_eq.symm

end

end ArtinMatthews.SourceEuler
