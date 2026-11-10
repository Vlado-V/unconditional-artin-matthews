module

public import Mathlib.Analysis.Complex.Basic
public import ArtinMatthews.FinitePiSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite-prime prefixes of an Euler series. A prefix is
identified with all local choices on that finite set, including the
zero choice. No factorization or coverage premise is supplied. -/

namespace ArtinMatthews.SourceEuler

open scoped BigOperators Classical
noncomputable section

variable {P X : Type} [Zero X]

def primeChoicePrefixEquiv (S : Finset P) :
    {a : P →₀ X // a.support ⊆ S} ≃ (S → X) where
  toFun a p := a.val p
  invFun g := ⟨Finsupp.onFinset S (fun p => if h : p ∈ S then g ⟨p, h⟩ else 0)
    (by intro p hp; by_contra hn; exact hp (dite_eq_right hn)),
    Finsupp.support_onFinset_subset⟩
  left_inv a := by
    apply Subtype.ext
    ext p
    by_cases hp : p ∈ S
    · simp only [Finsupp.onFinset_apply, dite_eq_left hp]
    · have ha : a.val p = 0 := by
        by_contra hn
        exact hp (a.property (Finsupp.mem_support_iff.mpr hn))
      simp only [Finsupp.onFinset_apply, dite_eq_right hp, ha]
  right_inv g := by
    funext p
    simp only [Finsupp.onFinset_apply, dite_eq_left p.property]

def finiteChoiceWeight (f : P → X → ℂ) (a : P →₀ X) : ℂ :=
  ∏ p ∈ a.support, f p (a p)

theorem finiteChoiceWeight_single (f : P → X → ℂ) (hf : ∀ p, f p 0 = 1)
    (p : P) (x : X) : finiteChoiceWeight f (Finsupp.single p x) = f p x := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [finiteChoiceWeight, hf]
  · simp [finiteChoiceWeight, Finsupp.support_single p hx]

theorem finiteChoiceWeight_eq_prefix (f : P → X → ℂ) (hf : ∀ p, f p 0 = 1)
    (S : Finset P) (a : P →₀ X) (ha : a.support ⊆ S) :
    finiteChoiceWeight f a = ∏ p ∈ S, f p (a p) := by
  classical
  apply Finset.prod_subset ha
  intro p hp hnot
  rw [Finsupp.notMem_support_iff.mp hnot, hf]

theorem localChoice_summable (f : P → X → ℂ) (hf : ∀ p, f p 0 = 1)
    (hs : Summable (fun a : P →₀ X => ‖finiteChoiceWeight f a‖)) (p : P) :
    Summable (fun x : X => ‖f p x‖) := by
  classical
  have h := hs.comp_injective (Finsupp.single_injective (a := p))
  change Summable (fun x : X => ‖finiteChoiceWeight f (Finsupp.single p x)‖) at h
  simpa only [finiteChoiceWeight_single f hf] using h

theorem finiteChoice_prefix_sum (f : P → X → ℂ) (hf : ∀ p, f p 0 = 1)
    (hs : Summable (fun a : P →₀ X => ‖finiteChoiceWeight f a‖)) (S : Finset P) :
    (∑' a : {a : P →₀ X // a.support ⊆ S}, finiteChoiceWeight f a.val) =
      ∏ p ∈ S, ∑' x : X, f p x := by
  classical
  let e := primeChoicePrefixEquiv (X := X) S
  have hp (g : S → X) : finiteChoiceWeight f (e.symm g).val = ∏ p : S, f p (g p) := by
    rw [finiteChoiceWeight_eq_prefix f hf S _ (e.symm g).property, ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro p _
    have h := congrFun (e.apply_symm_apply g) p
    exact congrArg (f p) h
  calc
    _ = ∑' g : S → X, finiteChoiceWeight f (e.symm g).val := (e.symm.tsum_eq _).symm
    _ = ∑' g : S → X, ∏ p : S, f p (g p) := tsum_congr hp
    _ = ∏ p : S, ∑' x : X, f p x :=
      (finitePiSeries S X (fun p => f p) (fun p => localChoice_summable f hf hs p)).2
    _ = _ := Finset.prod_coe_sort S (fun p => ∑' x : X, f p x)

end

end ArtinMatthews.SourceEuler
