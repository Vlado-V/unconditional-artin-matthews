module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Module.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! An absolutely summable four-coordinate product, with heterogeneous domains. -/
namespace ArtinMatthews.SourceEuler
variable {A B C D : Type}

theorem fourProduct_summable (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) (k : D → ℝ)
    (hf : Summable f) (hg : Summable g) (hh : Summable h) (hk : Summable k) :
    Summable (fun a : A × B × C × D => f a.1 * (g a.2.1 * (h a.2.2.1 * k a.2.2.2))) := by
  have hhk : Summable (fun a : C × D => h a.1 * k a.2) :=
    summable_mul_of_summable_norm (f := h) (g := k) hh.norm hk.norm
  have hghk : Summable (fun a : B × C × D => g a.1 * (h a.2.1 * k a.2.2)) :=
    summable_mul_of_summable_norm (f := g) (g := fun a : C × D => h a.1 * k a.2)
      hg.norm hhk.norm
  exact summable_mul_of_summable_norm (f := f)
    (g := fun a : B × C × D => g a.1 * (h a.2.1 * k a.2.2)) hf.norm hghk.norm

end ArtinMatthews.SourceEuler
