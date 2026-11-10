module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.FiniteProductTonelli
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence for the finite product of genuine countable rows. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

theorem finiteProduct_summable_nonneg {ι : Type*} [Fintype ι]
    (X : ι → Type*) (f : ∀ i, X i → ℝ)
    (hf0 : ∀ i x, 0 ≤ f i x) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : ∀ i, X i => ∏ i, f i (x i)) := by
  classical
  have he : (∑' x : ∀ i, X i, ENNReal.ofReal (∏ i, f i (x i))) =
      ∏ i, ∑' x : X i, ENNReal.ofReal (f i x) := by
    calc
      _ = ∑' x : ∀ i, X i, ∏ i, ENNReal.ofReal (f i (x i)) := by
        apply tsum_congr
        intro x
        exact ENNReal.ofReal_prod_of_nonneg (fun i _ => hf0 i (x i))
      _ = _ := finiteProduct_tsum_prod X (fun i x => ENNReal.ofReal (f i x))
  have hn : (∑' x : ∀ i, X i, ENNReal.ofReal (∏ i, f i (x i))) ≠ ∞ := by
    rw [he]
    exact ENNReal.prod_ne_top (fun i _ => (hf i).tsum_ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => hf0 i _))] using
    ENNReal.summable_toReal hn

theorem finiteProduct_summable_norm {ι : Type*} [Fintype ι]
    (X : ι → Type*) (f : ∀ i, X i → ℂ)
    (hf : ∀ i, Summable (fun x => ‖f i x‖)) :
    Summable (fun x : ∀ i, X i => ‖∏ i, f i (x i)‖) := by
  simpa only [norm_prod] using
    finiteProduct_summable_nonneg X (fun i x => ‖f i x‖) (fun _ _ => norm_nonneg _) hf

end
end ArtinMatthews
