module

public import ArtinMatthews.GiantSignedChronologicalLineage
public import ArtinMatthews.GiantSignedChronologicalFrameBound


set_option backward.privateInPublic true
@[expose] public section

/-! Exact support of the distinct-birth chronology. Its active lists
are distinct and every realized memory lies in the finite band bound. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

theorem giantSignedChronologicalMarking_distinct (κ : Fin n → ℤ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h)) (i : Fin (n+1)) :
    MarkedPhysicalMarkingDistinct (h.state i).2.1 := by
  intro g u v huv
  have hLive := giantSignedBirthLineage_injective
    (giantSignedChronologicalPreLineage h κ ha i g) hd
  exact Sum.inl.inj (hLive (show giantSignedStateLivePrime (h.state i) g (.inl u) =
    giantSignedStateLivePrime (h.state i) g (.inl v) from huv))

theorem giantSignedChronologicalMemoryCap_of_distinct (κ : Fin n → ℤ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h)) :
    GiantSignedChronologicalMemoryCap (∑ g, (PB g).card) h := by
  constructor <;> intro i <;> apply Finset.sum_le_sum <;> intro g _
  · exact (Nat.le_add_left _ _).trans (giantSignedChronological_distinct_degrees h κ ha hd i g).1
  · exact (Nat.le_add_left _ _).trans (giantSignedChronological_distinct_degrees h κ ha hd i g).2.1

theorem giantSignedChronologicalDistinctWeight_support_cap (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hw : giantSignedChronologicalDistinctWeight ν V κ q visitQ ρ θ ζ K h ≠ 0) :
    GiantSignedChronologicalMemoryCap (∑ g, (PB g).card) h := by
  classical
  have hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h) := by
    by_contra hbad
    exact hw (ite_eq_right hbad)
  rw [giantSignedChronologicalDistinctWeight, ite_eq_left hd] at hw
  exact giantSignedChronologicalMemoryCap_of_distinct h κ
    (giantSignedChronologicalWeight_admissible ν V κ q visitQ ρ θ ζ K h hw) hd

end
end ArtinMatthews
