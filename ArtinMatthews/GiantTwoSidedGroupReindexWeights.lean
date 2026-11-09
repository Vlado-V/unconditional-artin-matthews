module

public import ArtinMatthews.GiantTwoSidedGroupReindexData
public import ArtinMatthews.GiantTwoSidedResiduePrimeFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The numerical primes, original independent residue mean, and all
original path weights are preserved by relabeling the group indices. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {A J : Type*} [Fintype A] [Fintype J] (e : A ≃ J) (P : J → Finset ℕ)

theorem giantTwoSidedIndependentResidueMean_pull
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    [∀ p : ↥(markedPhysicalBandPrimes (P ∘ e)), NeZero p.val]
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (q : ℝ) (offset : Fin (n+1) → ℤ) :
    giantTwoSidedIndependentResidueMean (fun i => giantTwoSidedPullMarking e P M (labels i)) q offset =
      giantTwoSidedIndependentResidueMean labels q offset := by
  have hpull : Pairwise (fun i j => Disjoint ((P ∘ e) i) ((P ∘ e) j)) :=
    fun _ _ h => hdis (fun he => h (e.injective he))
  unfold giantTwoSidedIndependentResidueMean
  rw [giantTwoSidedIndependentResidue_mean_product hpull,
    giantTwoSidedIndependentResidue_mean_product hdis, giantTwoSidedPull_bandPrimes e P]
  apply Finset.prod_congr rfl
  intro p hp
  letI : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : ↥(markedPhysicalBandPrimes P)).val)
  rw [giantTwoSidedIndependentPrimeMean_eq, giantTwoSidedIndependentPrimeMean_eq]
  simp only [giantTwoSidedIndependentPrimeFactor, giantTwoSidedPull_activePrimes]

theorem giantTwoSidedPull_permuteLabels {M : ℕ} (π : J → Equiv.Perm (Fin M))
    (a : MarkedPhysicalMarking P M) :
    giantTwoSidedPermuteLabels (giantTwoSidedPullSlots e M π) (giantTwoSidedPullMarking e P M a) =
      giantTwoSidedPullMarking e P M (giantTwoSidedPermuteLabels π a) := by
  funext j i
  simp only [giantTwoSidedPermuteLabels, giantTwoSidedPullMarking_apply, giantTwoSidedPullSlots_apply]

variable {k ell n : ℕ}

theorem giantTwoSidedPull_dilation (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) (aux : GiantTwoSidedPatternAuxiliary P C) :
    giantTwoSidedPatternDilation (C ∘ e) (giantTwoSidedPullMarking e P (k+ell) a)
      (giantTwoSidedPullAuxiliary e P C aux) = giantTwoSidedPatternDilation C a aux := by
  unfold giantTwoSidedPatternDilation giantTwoSidedPatternCopiedProduct giantTwoSidedPatternAuxiliaryProduct
  simp only [Function.comp_apply, giantTwoSidedPullMarking_apply, giantTwoSidedPullAuxiliary_apply]
  exact congrArg₂ (·*·)
    (e.prod_comp (fun j => ∏ i ∈ Finset.univ \ C j, (a j (Fin.castAdd ell i)).val))
    (e.prod_comp (fun j => ∏ i : ↥(C j), (aux j i).val))

theorem giantTwoSidedPull_increment (C : Fin n → J → Finset (Fin k))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
    (π : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (κ : Fin n → ℤ) :
    giantTwoSidedLabelIncrement (fun i => C i ∘ e)
      (fun i => giantTwoSidedPullMarking e P (k+ell) (labels i))
      (fun i => giantTwoSidedPullSlots e (k+ell) (π i))
      (fun i => giantTwoSidedPullAuxiliary e P (C i) (aux i)) κ =
      giantTwoSidedLabelIncrement C labels π aux κ := by
  funext i
  simp only [giantTwoSidedLabelIncrement, giantTwoSidedPull_permuteLabels, giantTwoSidedPull_dilation]

theorem giantTwoSidedPull_rootScalar (C : Fin n → J → Finset (Fin k))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient P (C i) ell) :
    giantTwoSidedRootScalar (fun i => C i ∘ e) (fun i => giantTwoSidedPullMarking e P (k+ell) (labels i))
      (fun i => giantTwoSidedPullSlots e (k+ell) (π i)) (fun i => giantTwoSidedPullSlots e (k+ell) (τ i))
      (fun i => giantTwoSidedPullAuxiliary e P (C i) (aux i)) ζ
      (fun i => giantTwoSidedPullCoefficient e P (K i)) =
      giantTwoSidedRootScalar C labels π τ aux ζ K := by
  have hm : markedPhysicalMass (fun a => bandReciprocalMass ((P ∘ e) a)) (k+ell) =
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) :=
    e.prod_comp (fun j => (bandReciprocalMass (P j))⁻¹^(k+ell))
  have ha (i : Fin n) : giantTwoSidedPatternAuxiliaryMass (giantTwoSidedPullAuxiliary e P (C i) (aux i)) =
      giantTwoSidedPatternAuxiliaryMass (aux i) := by
    simp only [giantTwoSidedPatternAuxiliaryMass, Function.comp_apply, giantTwoSidedPullAuxiliary_apply]
    exact e.prod_comp (fun j => ∏ l : ↥(C i j), markedHarmonicAtom (P j) (aux i j l))
  have hf (i : Fin n) : giantTwoSidedPatternFreshMass (P ∘ e) (C i ∘ e) ell =
      giantTwoSidedPatternFreshMass P (C i) ell :=
    e.prod_comp (fun j => (bandReciprocalMass (P j))⁻¹^(ell+(C i j).card))
  simp only [giantTwoSidedRootScalar, hm, ha, hf, giantTwoSidedPull_permuteLabels,
    giantTwoSidedPull_dilation, giantTwoSidedPullCoefficient, Equiv.symm_apply_apply]

end
end ArtinMatthews
