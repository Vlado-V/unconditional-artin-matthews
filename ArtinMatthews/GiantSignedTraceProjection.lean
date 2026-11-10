module

public import ArtinMatthews.GiantSignedTraceSum
public import Mathlib.Analysis.Normed.Group.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! Projection at both ends of every row is exactly the restriction of
the complete trace to its actual intermediate states. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v
variable {X : Type u}

def giantSignedTraceProject (good : X → Prop) (f : X → ℂ) (x : X) : ℂ :=
  if good x then f x else 0

def giantSignedTraceProjectedRowApply (good : X → Prop)
    (r : GiantSignedTraceRow.{u,v} X) (f : X → ℂ) : X → ℂ :=
  giantSignedTraceProject good (giantSignedTraceRowApply r (giantSignedTraceProject good f))

def giantSignedTraceProjectedWord (good : X → Prop) (rs : List (GiantSignedTraceRow.{u,v} X))
    (f : X → ℂ) : X → ℂ :=
  rs.foldr (giantSignedTraceProjectedRowApply good) f

def GiantSignedTraceWithin (good : X → Prop) :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → (x : X) → GiantSignedTrace rs x → Prop
  | [], _, _ => True
  | r :: rs, x, ⟨m,t⟩ => good x ∧ good (r.target x m) ∧
      GiantSignedTraceWithin good rs (r.target x m) t

private def giantSignedTraceIndicator (p : Prop) (z : ℂ) : ℂ := if p then z else 0

private theorem giantSignedTraceProjection_sigma {A : Type*} {T : A → Type*}
    (g : Prop) (G : A → Prop) (J : (a : A) → T a → Prop)
    (c : A → ℂ) (F : (a : A) → T a → ℂ)
    (h : Summable (fun z : Σ a, T a => ‖c z.1 * F z.1 z.2‖)) :
    (∑' z : Σ a, T a, giantSignedTraceIndicator (g ∧ G z.1 ∧ J z.1 z.2) (c z.1 * F z.1 z.2)) =
      giantSignedTraceIndicator g (∑' a,
        c a * giantSignedTraceIndicator (G a) (∑' b : T a, giantSignedTraceIndicator (J a b) (F a b))) := by
  unfold giantSignedTraceIndicator
  have hs : Summable (fun z : Σ a, T a =>
      ‖@ite ℂ (g ∧ G z.1 ∧ J z.1 z.2) (Classical.propDecidable _) (c z.1 * F z.1 z.2) 0‖) :=
    h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => by
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (c z.1 * F z.1 z.2))
  rw [hs.of_norm.tsum_sigma]
  by_cases hg : g
  · rw [ite_eq_left hg]
    apply tsum_congr
    intro a
    by_cases ha : G a
    · rw [ite_eq_left ha, ← tsum_mul_left]
      exact tsum_congr (fun b => by simp only [hg, ha, true_and, mul_ite, mul_zero])
    · simp only [hg, ha, true_and, false_and, ite_false, mul_zero, tsum_zero]
  · simp only [hg, false_and, ite_false, tsum_zero]

theorem giantSignedTraceProjectedWord_eq (degree : X → ℕ) (f : X → ℂ)
    (hf : GiantSignedTraceExponential degree (fun x => ‖f x‖))
    (rs : List (GiantSignedTraceRow.{u,v} X))
    (hr : ∀ r ∈ rs, GiantSignedTraceRowAbsolute degree r) (good : X → Prop) (x : X) :
    giantSignedTraceProjectedWord good rs f x = ∑' t : GiantSignedTrace rs x,
      if GiantSignedTraceWithin good rs x t then giantSignedTraceWeight f rs x t else 0 := by
  induction rs generalizing x with
  | nil =>
      change f x = ∑' _ : PUnit.{v+1}, @ite ℂ True (Classical.propDecidable True) (f x) 0
      simp only [ite_true, tsum_fintype, Fintype.sum_unique]
  | cons r rs ih =>
      have hs := (giantSignedTrace_summable_eq degree f hf (r::rs) hr).1 x
      have h := giantSignedTraceProjection_sigma (good x) (fun m => good (r.target x m))
        (fun m => GiantSignedTraceWithin good rs (r.target x m)) (r.coefficient x)
        (fun m => giantSignedTraceWeight f rs (r.target x m)) hs
      refine Eq.trans ?_ h.symm
      unfold giantSignedTraceIndicator
      by_cases hg : good x
      · change (if good x then _ else 0) = _
        rw [ite_eq_left hg, ite_eq_left hg]
        apply tsum_congr
        intro m
        exact congrArg (fun z => r.coefficient x m * (if good (r.target x m) then z else 0))
          (ih (fun a ha => hr a (List.mem_cons_of_mem _ ha)) (r.target x m))
      · change (if good x then _ else 0) = _
        rw [ite_eq_right hg, ite_eq_right hg]

end
end ArtinMatthews
