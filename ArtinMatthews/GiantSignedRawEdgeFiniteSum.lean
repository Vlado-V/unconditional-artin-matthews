module

public import ArtinMatthews.GiantSignedRawEdgeLinear


set_option backward.privateInPublic true
@[expose] public section

/-! Finite test sums commute with the literal full raw edge family. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B I : Type*} [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedRawEdgeFamilyApply_finset_sum {A : Type*}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (patterns : Finset I) (C : I → B → Finset (Fin k)) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (T : Finset A) (f : A → GiantSignedState PS PB (k+ell) → ℂ)
    (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η
      (fun t => ∑ a ∈ T, f a t) s =
        ∑ a ∈ T, giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η (f a) s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, giantSignedRawEdgeFamilyApply_zero]
  | @insert a T ha ih =>
      simp only [Finset.sum_insert ha, giantSignedRawEdgeFamilyApply_add, ih]

end
end ArtinMatthews
