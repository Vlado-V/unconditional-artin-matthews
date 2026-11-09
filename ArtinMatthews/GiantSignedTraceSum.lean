module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! A finite word of countable rows expands on dependent move traces.
The state of each following row is the actual target of the preceding move. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

universe u v

structure GiantSignedTraceRow (X : Type u) where
  Move : X → Type v
  target : (x : X) → Move x → X
  coefficient : (x : X) → Move x → ℂ
  batchSize : (x : X) → Move x → ℕ

variable {X : Type u}

def GiantSignedTrace : List (GiantSignedTraceRow.{u,v} X) → X → Type v
  | [], _ => PUnit
  | r :: rs, x => Σ m : r.Move x, GiantSignedTrace rs (r.target x m)

def giantSignedTraceWeight (f : X → ℂ) :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → (x : X) → GiantSignedTrace rs x → ℂ
  | [], x, _ => f x
  | r :: rs, x, ⟨m,t⟩ => r.coefficient x m * giantSignedTraceWeight f rs (r.target x m) t

def giantSignedTraceBatchSize :
    (rs : List (GiantSignedTraceRow.{u,v} X)) → (x : X) → GiantSignedTrace rs x → ℕ
  | [], _, _ => 0
  | r :: rs, x, ⟨m,t⟩ => max (r.batchSize x m) (giantSignedTraceBatchSize rs (r.target x m) t)

def giantSignedTraceRowApply (r : GiantSignedTraceRow.{u,v} X) (f : X → ℂ) (x : X) : ℂ :=
  ∑' m : r.Move x, r.coefficient x m * f (r.target x m)

def giantSignedTraceWord (rs : List (GiantSignedTraceRow.{u,v} X)) (f : X → ℂ) : X → ℂ :=
  rs.foldr giantSignedTraceRowApply f

def giantSignedTraceRowMass (r : GiantSignedTraceRow.{u,v} X) (f : X → ℝ) (x : X) : ℝ :=
  ∑' m : r.Move x, ‖r.coefficient x m‖ * f (r.target x m)

def giantSignedTraceMass (rs : List (GiantSignedTraceRow.{u,v} X)) (f : X → ℂ) (x : X) : ℝ :=
  ∑' t : GiantSignedTrace rs x, ‖giantSignedTraceWeight f rs x t‖

def GiantSignedTraceExponential (degree : X → ℕ) (f : X → ℝ) : Prop :=
  ∃ C u : ℝ, 0 ≤ C ∧ 0 < u ∧ ∀ x, f x ≤ C * u ^ degree x

def GiantSignedTraceRowAbsolute (degree : X → ℕ) (r : GiantSignedTraceRow.{u,v} X) : Prop :=
  ∀ f : X → ℝ, (∀ x, 0 ≤ f x) → GiantSignedTraceExponential degree f →
    (∀ x, Summable (fun m : r.Move x => ‖r.coefficient x m‖ * f (r.target x m))) ∧
      GiantSignedTraceExponential degree (giantSignedTraceRowMass r f)

private theorem giantSignedTrace_sigma_sum {A : Type*} {T : A → Type*}
    (c : A → ℂ) (F : (a : A) → T a → ℂ)
    (hF : ∀ a, Summable (fun b : T a => ‖F a b‖))
    (hc : Summable (fun a => ‖c a‖ * ∑' b : T a, ‖F a b‖)) :
    Summable (fun z : Σ a, T a => ‖c z.1 * F z.1 z.2‖) ∧
      (∑' z : Σ a, T a, ‖c z.1 * F z.1 z.2‖) =
        (∑' a, ‖c a‖ * ∑' b : T a, ‖F a b‖) ∧
      (∑' z : Σ a, T a, c z.1 * F z.1 z.2) = ∑' a, c a * ∑' b : T a, F a b := by
  have hs : Summable (fun z : Σ a, T a => ‖c z.1 * F z.1 z.2‖) := by
    simp only [norm_mul]
    refine (summable_sigma_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      ⟨fun a => (hF a).mul_left ‖c a‖, ?_⟩
    simpa only [tsum_mul_left] using hc
  refine ⟨hs, ?_, ?_⟩
  · rw [hs.tsum_sigma]
    simp only [norm_mul, tsum_mul_left]
  · rw [hs.of_norm.tsum_sigma]
    simp only [tsum_mul_left]

theorem giantSignedTrace_summable_eq (degree : X → ℕ) (f : X → ℂ)
    (hf : GiantSignedTraceExponential degree (fun x => ‖f x‖))
    (rs : List (GiantSignedTraceRow.{u,v} X))
    (hr : ∀ r ∈ rs, GiantSignedTraceRowAbsolute degree r) :
    (∀ x, Summable (fun t : GiantSignedTrace rs x => ‖giantSignedTraceWeight f rs x t‖)) ∧
      GiantSignedTraceExponential degree (giantSignedTraceMass rs f) ∧
      ∀ x, (∑' t : GiantSignedTrace rs x, giantSignedTraceWeight f rs x t) =
        giantSignedTraceWord rs f x := by
  induction rs with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · intro x
        change Summable (fun _ : PUnit.{v+1} => ‖f x‖)
        exact (hasSum_fintype _).summable
      · change GiantSignedTraceExponential degree (fun x => ∑' _ : PUnit.{v+1}, ‖f x‖)
        simpa only [tsum_fintype, Fintype.sum_unique] using hf
      · intro x
        change (∑' _ : PUnit.{v+1}, f x) = f x
        simp only [tsum_fintype, Fintype.sum_unique]
  | cons r rs ih =>
      obtain ⟨ht, hg, he⟩ := ih (fun a ha => hr a (List.mem_cons_of_mem _ ha))
      let g := giantSignedTraceMass rs f
      have hg0 : ∀ x, 0 ≤ g x := fun x => tsum_nonneg (fun _ => norm_nonneg _)
      obtain ⟨hs, hG⟩ := hr r List.mem_cons_self g hg0 hg
      have h (x : X) := giantSignedTrace_sigma_sum (r.coefficient x)
        (fun m => giantSignedTraceWeight f rs (r.target x m))
        (fun m => ht (r.target x m)) (hs x)
      refine ⟨fun x => (h x).1, ?_, ?_⟩
      · have hmass : giantSignedTraceMass (r::rs) f = giantSignedTraceRowMass r g :=
          funext (fun x => (h x).2.1)
        rw [hmass]
        exact hG
      · intro x
        refine (h x).2.2.trans ?_
        exact tsum_congr (fun m => congrArg (fun z => r.coefficient x m * z) (he (r.target x m)))

theorem giantSignedTraceCutoff_tendsto (f : X → ℂ)
    (rs : List (GiantSignedTraceRow.{u,v} X)) (x : X)
    (hf : Summable (fun t : GiantSignedTrace rs x => ‖giantSignedTraceWeight f rs x t‖)) :
    Tendsto (fun H : ℕ => ∑' t : GiantSignedTrace rs x,
      if giantSignedTraceBatchSize rs x t ≤ H then giantSignedTraceWeight f rs x t else 0)
      atTop (𝓝 (∑' t : GiantSignedTrace rs x, giantSignedTraceWeight f rs x t)) := by
  apply tendsto_tsum_of_dominated_convergence hf
  · intro t
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (giantSignedTraceBatchSize rs x t)] with H hH
    exact (ite_eq_left hH).symm
  · exact Filter.Eventually.of_forall fun H t => by
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (giantSignedTraceWeight f rs x t)

end
end ArtinMatthews
