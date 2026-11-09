module

public import ArtinMatthews.GiantSignedChronologicalStatic
public import ArtinMatthews.GiantTwoSidedResiduePathFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The small coordinates retain the original two half dampings and the
same integer offsets as the joined chronological path. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

theorem giantSignedChronologicalSmall_damping_factor
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun a b => Disjoint (PS a) (PS b)))
    {q : ℝ} (hq : 0 ≤ q) (hn : 0 < n)
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (hc : GiantSignedChronologicalCompatible κ h) :
    (∏ i : Fin n,
      giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallSource h i).val.1 *
        giantTwoSidedResidueDamping PS (k+ell) q (giantSignedChronologicalSmallTarget h i).val.1) =
      giantTwoSidedIndependentResidueFactor PS (fun v => (h.state v).1.val.2) q
        (giantSignedChronologicalJoinedOffset h κ) (h.state 0).1.val.1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  change (∏ i : Fin (m+1),
    giantTwoSidedResidueDamping PS (k+ell) q (h.state i.castSucc).1.val.1 *
      giantTwoSidedResidueDamping PS (k+ell) q (h.state i.succ).1.val.1) = _
  rw [giantTwoSidedResiduePath_damping_schedule hPS hdis hq (fun v => (h.state v).1)]
  unfold giantTwoSidedIndependentResidueFactor
  apply Finset.prod_congr rfl
  intro v _
  have ha : giantTwoSidedResidueActiveIndicator (h.state v).1.val.2
      (giantTwoSidedResidueTranslate (giantSignedChronologicalJoinedOffset h κ v)
        (h.state 0).1.val.1) = 1 := by
    rw [← giantSignedChronologicalSmallResidue_eq_translate h κ hc v,
      giantTwoSidedResidueActiveIndicator_eq, ite_eq_left (h.state v).1.property.2]
  rw [ha, one_mul, ← giantSignedChronologicalSmallResidue_eq_translate h κ hc v]

end
end ArtinMatthews
