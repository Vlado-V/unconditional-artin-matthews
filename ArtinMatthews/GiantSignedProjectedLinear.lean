module

public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.GiantSignedCappedStateDomain
public import ArtinMatthews.GiantSignedVisitLinear
public import ArtinMatthews.GiantSignedRawEdgeFiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! The literal projected local operations commute with finite sums.
Finiteness of the retained states supplies the visit's absolute convergence. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

section Cutoff
variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedStateMemoryCutoff_finset_sum {A : Type*}
    (N : ℕ) (T : Finset A) (f : A → GiantSignedState PS PB M → ℂ) :
    giantSignedStateMemoryCutoff N (fun s => ∑ a ∈ T, f a s) =
      fun s => ∑ a ∈ T, giantSignedStateMemoryCutoff N (f a) s := by
  funext s
  unfold giantSignedStateMemoryCutoff
  split_ifs <;> simp only [Finset.sum_const_zero]

theorem giantSignedStateMemoryCutoff_zero (N : ℕ) :
    giantSignedStateMemoryCutoff N (fun _ : GiantSignedState PS PB M => 0) = fun _ => 0 := by
  funext s
  unfold giantSignedStateMemoryCutoff
  split_ifs <;> rfl

end Cutoff

section Visit
variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [Fintype (GiantTwoSidedResidueState PS M)]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedProjectedVisit_add (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    (f g : GiantSignedState PS PB M → ℂ) :
    giantSignedProjectedVisit N ν V q ρ (fun s => f s + g s) =
      fun s => giantSignedProjectedVisit N ν V q ρ f s +
        giantSignedProjectedVisit N ν V q ρ g s := by
  unfold giantSignedProjectedVisit
  have hcut := giantSignedStateMemoryCutoff_add N f g
  change giantSignedStateMemoryCutoff N (fun s => f s + g s) =
    (fun s => giantSignedStateMemoryCutoff N f s + giantSignedStateMemoryCutoff N g s) at hcut
  rw [hcut]
  rw [giantSignedChronologicalVisit_add ν hν V q ρ
    (giantSignedStateMemoryCutoff_exponential N f)
    (giantSignedStateMemoryCutoff_exponential N g)]
  exact giantSignedStateMemoryCutoff_add N _ _

theorem giantSignedProjectedVisit_finset_sum {A : Type*} (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    (T : Finset A) (f : A → GiantSignedState PS PB M → ℂ) :
    giantSignedProjectedVisit N ν V q ρ (fun s => ∑ a ∈ T, f a s) =
      fun s => ∑ a ∈ T, giantSignedProjectedVisit N ν V q ρ (f a) s := by
  unfold giantSignedProjectedVisit
  rw [giantSignedStateMemoryCutoff_finset_sum]
  rw [giantSignedChronologicalVisit_finset_sum ν hν V q ρ T
    (fun a => giantSignedStateMemoryCutoff N (f a))
    (fun a _ => giantSignedStateMemoryCutoff_exponential N (f a))]
  exact giantSignedStateMemoryCutoff_finset_sum N T _

end Visit

section Edge
variable {S B I : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedProjectedRawEdgeFamilyApply_add (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f g : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η
      (fun s => f s + g s) = fun s =>
      giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η f s +
        giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η g s := by
  unfold giantSignedProjectedRawEdgeFamilyApply
  have hcut := giantSignedStateMemoryCutoff_add N f g
  change giantSignedStateMemoryCutoff N (fun s => f s + g s) =
    (fun s => giantSignedStateMemoryCutoff N f s + giantSignedStateMemoryCutoff N g s) at hcut
  rw [hcut]
  have h := funext (giantSignedRawEdgeFamilyApply_add ν V patterns C κ q ρ θ ζ K η
    (giantSignedStateMemoryCutoff N f) (giantSignedStateMemoryCutoff N g))
  rw [h]
  exact giantSignedStateMemoryCutoff_add N _ _

theorem giantSignedProjectedRawEdgeFamilyApply_finset_sum {A : Type*} (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (T : Finset A) (f : A → GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η
      (fun s => ∑ a ∈ T, f a s) = fun s =>
      ∑ a ∈ T, giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η (f a) s := by
  unfold giantSignedProjectedRawEdgeFamilyApply
  rw [giantSignedStateMemoryCutoff_finset_sum]
  have h := funext (giantSignedRawEdgeFamilyApply_finset_sum ν V patterns C κ q ρ θ ζ K η
    T (fun a => giantSignedStateMemoryCutoff N (f a)))
  rw [h]
  exact giantSignedStateMemoryCutoff_finset_sum N T _

theorem giantSignedProjectedRawEdgeFamilyApply_clean_add_dirty (N : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k))
    (κ : ℤ) (q ρ θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K η f =
      fun s => giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K
        (fun i s r => η i s r * giantSignedRawEdgeCleanMultiplier s r) f s +
      giantSignedProjectedRawEdgeFamilyApply N ν V patterns C κ q ρ θ ζ K
        (fun i s r => η i s r * giantSignedRawEdgeDirtyMultiplier s r) f s := by
  unfold giantSignedProjectedRawEdgeFamilyApply
  have h := funext (giantSignedRawEdgeFamilyApply_clean_add_dirty ν V patterns C κ q ρ θ ζ K η
    (giantSignedStateMemoryCutoff N f))
  rw [h]
  exact giantSignedStateMemoryCutoff_add N _ _

end Edge
end
end ArtinMatthews
