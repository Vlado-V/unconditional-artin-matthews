module

public import ArtinMatthews.GiantSignedChronologicalLifespanNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The literal distinct chronological weight with the small and phase factors displayed separately. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B] [DecidableEq S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

def giantSignedChronologicalEdgeExterior (κ : Fin n → ℤ) (q θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) (i : Fin n) : ℂ :=
  (giantTwoSidedResidueSlotNormalization (J := S) (k+ell) : ℂ) *
    (giantTwoSidedResidueSlotNormalization (J := B) (k+ell) : ℂ) *
    (∏ g : S, ((bandReciprocalMass (PS g))⁻¹ : ℂ)^ell) *
    (giantTwoSidedPatternAuxiliaryMass (h.auxiliary i) : ℂ) *
    K i (giantSignedChronologicalBigSource h i) (giantSignedChronologicalBigTarget h i)
      (h.auxiliary i) *
    (giantSignedChronologicalProduct h i : ℂ)^((ζ i : ℂ)*Complex.I) *
    idealAdditivePhase (θ * (κ i : ℝ)) (giantSignedChronologicalProduct h i) *
    (giantTwoSidedResidueDamping PS (k+ell) q
      (giantSignedChronologicalSmallSource h i).val.1 : ℂ) *
    (giantTwoSidedResidueDamping PS (k+ell) q
      (giantSignedChronologicalSmallTarget h i).val.1 : ℂ)

def giantSignedChronologicalExterior (κ : Fin n → ℤ) (q θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell) : ℂ :=
  (giantTwoSidedResidueHaarStateMass PS (k+ell) : ℂ) *
    ∏ i, giantSignedChronologicalEdgeExterior h κ q θ ζ K i

private theorem edge_coefficient_split (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : Fin n → ℤ)
    (q ρ θ : ℝ) (ζ : Fin n → ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (i : Fin n) :
    giantSignedChronologicalEdgeCoefficient ν V κ q ρ θ ζ K h i =
      giantSignedChronologicalEdgeExterior h κ q θ ζ K i *
        giantSignedChronologicalEdgeMemoryCoefficient ν V κ ρ h i := rfl

theorem giantSignedChronologicalWeight_eq_primeProduct (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (ha : GiantSignedChronologicalAdmissible κ h) :
    giantSignedChronologicalWeight ν V κ q visitQ ρ θ ζ K h =
      giantSignedChronologicalExterior h κ q θ ζ K *
        giantSignedChronologicalPrimeProduct h ν V κ visitQ ρ := by
  rw [giantSignedChronologicalWeight, ite_eq_left ⟨ha.compatible, ha.boundary⟩]
  have hi : (giantSignedStateMass PS ν (h.state 0) : ℂ) =
      (giantTwoSidedResidueHaarStateMass PS (k+ell) : ℂ) *
        (giantSignedActiveMass ν (h.state 0).2.1 : ℂ) := by
    rw [giantSignedStateMass, ha.boundary.1, giantSignedEmptyMemory_mass, mul_one, Complex.ofReal_mul]
  rw [hi]
  simp_rw [edge_coefficient_split h ν V κ q ρ θ ζ K]
  rw [Finset.prod_mul_distrib]
  unfold giantSignedChronologicalExterior giantSignedChronologicalPrimeProduct
  ac_rfl

theorem giantSignedChronologicalDistinctWeight_eq_lifespan
    {A : (g : B) → PB g → Finset (Fin (n+1))}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p)) (offset : Fin (n+1) → ℤ)
    (κ : Fin n → ℤ) (q : ℝ) (visitQ : Fin (n+1) → ℝ) (ρ θ : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))
    (data : GiantSignedChronologicalLifespanCoefficientData c h offset)
    (hw : ∀ g p, giantSignedResidueLifespanWeight p.val offset visitQ (A g p) (c g p) ≠ 0)
    (hV : ∀ g, bandReciprocalMass (PB g) ≠ 0) (hρ : ρ ≠ 0)
    (hb : ∀ g (p : PB g), giantSignedPrimeBaseline visitQ p.val ≠ 0) :
    giantSignedChronologicalDistinctWeight (fun g p => giantSignedTiltedPrimeLaw (PB g) visitQ p)
      (fun g => bandReciprocalMass (PB g)) κ q visitQ ρ θ ζ K h =
      giantSignedChronologicalExterior h κ q θ ζ K * giantSignedChronologicalBirthFactor batch *
        giantSignedChronologicalBandNormalization (fun g => bandReciprocalMass (PB g)) C ell *
        ∏ g, ∏ p : PB g,
          ((giantSignedResidueLifespanWeight p.val offset visitQ (A g p) (c g p) /
            giantSignedPrimeBaseline visitQ p.val : ℝ) : ℂ) := by
  rw [giantSignedChronologicalDistinctWeight, ite_eq_left hd,
    giantSignedChronologicalWeight_eq_primeProduct h _ _ κ q visitQ ρ θ ζ K ha,
    giantSignedChronologicalPrimeProduct_eq_source_lifespan c h offset κ visitQ ρ ha data hw hV hρ hb]
  ac_rfl

end
end ArtinMatthews
