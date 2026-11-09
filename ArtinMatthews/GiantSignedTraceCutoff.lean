module

public import ArtinMatthews.GiantSignedTraceSum


set_option backward.privateInPublic true
@[expose] public section

/-! A common bound on displayed batches can be placed on each row or
on the completed trace. Absolute convergence justifies both forms. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

universe u v
variable {X : Type u}

def giantSignedTraceCutoffRowApply (H : ℕ) (r : GiantSignedTraceRow.{u,v} X)
    (f : X → ℂ) (x : X) : ℂ :=
  ∑' m : r.Move x, if r.batchSize x m ≤ H then r.coefficient x m * f (r.target x m) else 0

def giantSignedTraceCutoffWord (H : ℕ) (rs : List (GiantSignedTraceRow.{u,v} X))
    (f : X → ℂ) : X → ℂ :=
  rs.foldr (giantSignedTraceCutoffRowApply H) f

private theorem giantSignedTraceCutoff_sigma {A : Type*} {T : A → Type*}
    (c : A → ℂ) (F : (a : A) → T a → ℂ) (d : A → ℕ) (e : (a : A) → T a → ℕ)
    (H : ℕ) (h : Summable (fun z : Σ a, T a => ‖c z.1 * F z.1 z.2‖)) :
    (∑' z : Σ a, T a, if max (d z.1) (e z.1 z.2) ≤ H then c z.1 * F z.1 z.2 else 0) =
      ∑' a, if d a ≤ H then c a * (∑' b : T a, if e a b ≤ H then F a b else 0) else 0 := by
  have hs : Summable (fun z : Σ a, T a =>
      ‖if max (d z.1) (e z.1 z.2) ≤ H then c z.1 * F z.1 z.2 else 0‖) :=
    h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => by
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (c z.1 * F z.1 z.2))
  rw [hs.of_norm.tsum_sigma]
  apply tsum_congr
  intro a
  by_cases ha : d a ≤ H
  · rw [ite_eq_left ha, ← tsum_mul_left]
    exact tsum_congr (fun b => by simp only [max_le_iff, ha, true_and, mul_ite, mul_zero])
  · simp only [max_le_iff, ha, false_and, ite_false, tsum_zero]

theorem giantSignedTraceCutoffWord_eq (degree : X → ℕ) (f : X → ℂ)
    (hf : GiantSignedTraceExponential degree (fun x => ‖f x‖))
    (rs : List (GiantSignedTraceRow.{u,v} X))
    (hr : ∀ r ∈ rs, GiantSignedTraceRowAbsolute degree r) (H : ℕ) (x : X) :
    giantSignedTraceCutoffWord H rs f x =
      ∑' t : GiantSignedTrace rs x,
        if giantSignedTraceBatchSize rs x t ≤ H then giantSignedTraceWeight f rs x t else 0 := by
  induction rs generalizing x with
  | nil =>
      change f x = ∑' _ : PUnit.{v+1}, if 0 ≤ H then f x else 0
      simp only [zero_le, ite_true, tsum_fintype, Fintype.sum_unique]
  | cons r rs ih =>
      have hs := (giantSignedTrace_summable_eq degree f hf (r::rs) hr).1 x
      have h := giantSignedTraceCutoff_sigma (r.coefficient x)
        (fun m => giantSignedTraceWeight f rs (r.target x m))
        (r.batchSize x) (fun m => giantSignedTraceBatchSize rs (r.target x m)) H hs
      refine Eq.trans ?_ h.symm
      apply tsum_congr
      intro m
      exact congrArg (fun z => if r.batchSize x m ≤ H then r.coefficient x m * z else 0)
        (ih (fun a ha => hr a (List.mem_cons_of_mem _ ha)) (r.target x m))

theorem giantSignedTraceCutoffWord_tendsto (degree : X → ℕ) (f : X → ℂ)
    (hf : GiantSignedTraceExponential degree (fun x => ‖f x‖))
    (rs : List (GiantSignedTraceRow.{u,v} X))
    (hr : ∀ r ∈ rs, GiantSignedTraceRowAbsolute degree r) (x : X) :
    Tendsto (fun H => giantSignedTraceCutoffWord H rs f x) atTop (𝓝 (giantSignedTraceWord rs f x)) := by
  have h := giantSignedTrace_summable_eq degree f hf rs hr
  rw [← h.2.2 x]
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall
    (fun H => (giantSignedTraceCutoffWord_eq degree f hf rs hr H x).symm))
      (giantSignedTraceCutoff_tendsto f rs x (h.1 x))

end
end ArtinMatthews
