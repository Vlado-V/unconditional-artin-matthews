module

public import ArtinMatthews.GiantTwoSidedGroupReindexWeights


set_option backward.privateInPublic true
@[expose] public section

/-! The original finite signed return-Fourier sum commutes with
reindexing groups. Both slot permutations and the auxiliary tuples remain. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A J : Type*} [Fintype A] [Fintype J] (e : A ≃ J) (P : J → Finset ℕ)
    {k ell n : ℕ}

theorem giantTwoSidedPull_labelCompatible_iff (C : J → Finset (Fin k))
    (s t : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    GiantTwoSidedLabelCompatible (C ∘ e) (giantTwoSidedPullMarking e P (k+ell) s)
      (giantTwoSidedPullMarking e P (k+ell) t) (giantTwoSidedPullAuxiliary e P C aux) ↔
      GiantTwoSidedLabelCompatible C s t aux := by
  constructor
  · intro h
    constructor
    · intro j i hi
      obtain ⟨a,rfl⟩ := e.surjective j
      simpa only [giantTwoSidedPullMarking_apply] using h.copied a i hi
    · intro g j i l
      obtain ⟨a,rfl⟩ := e.surjective g
      obtain ⟨b,rfl⟩ := e.surjective j
      simpa only [giantTwoSidedPullAuxiliary_apply, giantTwoSidedPullMarking_apply] using h.banned a b i l
  · intro h
    constructor
    · intro j i hi
      simpa only [giantTwoSidedPullMarking_apply] using h.copied (e j) i hi
    · intro g j i l
      simpa only [giantTwoSidedPullAuxiliary_apply, giantTwoSidedPullMarking_apply] using h.banned (e g) (e j) i l

theorem giantTwoSidedPull_staticLabels_iff (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell)) :
    GiantTwoSidedStaticLabels (fun i => C i ∘ e)
      (fun i => giantTwoSidedPullSlots e (k+ell) (π i)) (fun i => giantTwoSidedPullSlots e (k+ell) (τ i))
      (fun i => giantTwoSidedPullAuxiliary e P (C i) (aux i))
      (fun i => giantTwoSidedPullMarking e P (k+ell) (labels i)) ↔
      GiantTwoSidedStaticLabels C π τ aux labels := by
  have hd (a : MarkedPhysicalMarking P (k+ell)) :
      MarkedPhysicalMarkingDistinct (giantTwoSidedPullMarking e P (k+ell) a) ↔
        MarkedPhysicalMarkingDistinct a := by
    simp only [MarkedPhysicalMarkingDistinct, giantTwoSidedPullMarking_apply]
    exact ⟨fun h j => by obtain ⟨b,rfl⟩ := e.surjective j; exact h b, fun h j => h (e j)⟩
  simp only [GiantTwoSidedStaticLabels, hd, giantTwoSidedPull_permuteLabels,
    giantTwoSidedPull_labelCompatible_iff]

variable [DecidableEq A] [DecidableEq J]
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (P ∘ e)), NeZero p.val]

theorem giantTwoSidedIndependentFourierMoment_pull
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (C : Fin n → J → Finset (Fin k)) (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (κ : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedIndependentFourierMoment (fun i => C i ∘ e)
      (fun i => giantTwoSidedPullSlots e (k+ell) (π i)) (fun i => giantTwoSidedPullSlots e (k+ell) (τ i))
      (fun i => giantTwoSidedPullAuxiliary e P (C i) (aux i)) κ q ζ
      (fun i => giantTwoSidedPullCoefficient e P (K i)) θ =
      giantTwoSidedIndependentFourierMoment C π τ aux κ q ζ K θ := by
  let pull := Equiv.piCongrRight (fun _ : Fin (n+1) => giantTwoSidedPullMarking e P (k+ell))
  unfold giantTwoSidedIndependentFourierMoment
  rw [← pull.sum_comp]
  apply Finset.sum_congr rfl
  intro labels _
  have hlabels : pull labels = fun i => giantTwoSidedPullMarking e P (k+ell) (labels i) := rfl
  simp only [hlabels, giantTwoSidedPull_staticLabels_iff,
    giantTwoSidedPull_rootScalar, giantTwoSidedPull_increment, giantTwoSidedIndependentResidueMean_pull e P hdis]

theorem giantTwoSidedExpandedIndependentFourierMoment_pull {I : Type*}
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k)) (κ : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i p, GiantTwoSidedPatternCoefficient P (C i p) ell)
    (θ : AddCircle (1 : ℝ)) :
    giantTwoSidedExpandedIndependentFourierMoment patterns (fun i p => C i p ∘ e) κ q ζ
      (fun i p => giantTwoSidedPullCoefficient e P (K i p)) θ =
      giantTwoSidedExpandedIndependentFourierMoment patterns C κ q ζ K θ := by
  let pull := Equiv.piCongrRight (fun i : Fin n => giantTwoSidedPullEdgeChoice e P (ell := ell) (patterns i) (C i))
  unfold giantTwoSidedExpandedIndependentFourierMoment
  rw [giantTwoSidedPull_slotNormalization e, ← pull.sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro choice _
  exact giantTwoSidedIndependentFourierMoment_pull e P hdis
    (fun i => C i (choice i).1.val) (fun i => (choice i).2.1) (fun i => (choice i).2.2.1)
    (fun i => (choice i).2.2.2) κ q ζ (fun i => K i (choice i).1.val) θ

end
end ArtinMatthews
