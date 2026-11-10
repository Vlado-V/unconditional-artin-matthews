module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

theorem spectral_contDiffOn_of_hasDerivAt_tower (F : ℕ → ℝ → ℂ) {s : Set ℝ}
    (hs : IsOpen s) (hF : ∀ n : ℕ, ∀ x ∈ s, HasDerivAt (F n) (F (n + 1) x) x) :
    ∀ n : ℕ, ContDiffOn ℝ ∞ (F n) s := by
  have hall (m : ℕ) : ∀ n : ℕ, ContDiffOn ℝ m (F n) s := by
    induction m with
    | zero =>
        intro n
        exact contDiffOn_zero.mpr (fun x hx => (hF n x hx).continuousAt.continuousWithinAt)
    | succ m ih =>
        intro n
        rw [show ((m + 1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 by norm_cast,
          contDiffOn_succ_iff_deriv_of_isOpen hs]
        refine ⟨fun x hx => (hF n x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
        apply (ih (n + 1)).congr
        intro x hx
        exact (hF n x hx).deriv
  intro n
  exact contDiffOn_infty.mpr (fun m => hall m n)

end
end ArtinMatthews
