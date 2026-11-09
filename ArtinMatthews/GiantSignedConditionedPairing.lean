module

public import ArtinMatthews.GiantSignedPairingEnergy
public import ArtinMatthews.GiantSignedConditionedClean


set_option backward.privateInPublic true
@[expose] public section

/-! The conditioned clean form is paired over the original full residue,
active-label and pending-memory measure, with no degree restriction. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

abbrev GiantSignedConditionedIndex (k ell : ℕ) :=
  MarkedPhysicalMarking PS k × (GiantSignedMemory PB ×
    (GiantTwoSidedFullResidue PS × MarkedPhysicalMarking PB (k+ell)))

def giantSignedConditionedWeight {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (i : GiantSignedConditionedIndex PS (PB := PB) k ell) : ℝ :=
  giantSignedSmallHaar PS * giantSignedMemoryMass ν i.2.1 * giantSignedActiveMass ν i.2.2.2

def giantSignedConditionedValue {k ell : ℕ}
    (F : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (i : GiantSignedConditionedIndex PS (PB := PB) k ell) : ℂ :=
  F i.1 i.2.2.1 i.2.2.2 i.2.1

def giantSignedConditionedEnergy {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (F : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ) : ℝ≥0∞ :=
  ∑' i : GiantSignedConditionedIndex PS (PB := PB) k ell,
    ENNReal.ofReal (giantSignedConditionedWeight PS ν i * ‖giantSignedConditionedValue PS F i‖ ^ 2)

def giantSignedConditionedPairing {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ) : ℂ :=
  ∑' i : GiantSignedConditionedIndex PS (PB := PB) k ell,
    (giantSignedConditionedWeight PS ν i : ℂ) *
      star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i

omit [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedConditionedWeight_nonneg {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (i : GiantSignedConditionedIndex PS (PB := PB) k ell) :
    0 ≤ giantSignedConditionedWeight PS ν i :=
  mul_nonneg (mul_nonneg (giantSignedSmallHaar_nonneg PS)
    (giantSignedMemoryMass_nonneg ν hν i.2.1))
    (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun j _ => hν g (i.2.2.2 g j))

theorem giantSignedConditionedEnergy_eq {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (F : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ) :
    giantSignedConditionedEnergy PS ν F =
      ∑ d : MarkedPhysicalMarking PS k, giantSignedAmbientEnergy PS ν (F d) := by
  simp only [giantSignedConditionedEnergy, GiantSignedConditionedIndex,
    ENNReal.tsum_prod', tsum_fintype, Fintype.sum_prod_type, giantSignedConditionedWeight,
    giantSignedConditionedValue, giantSignedAmbientEnergy]

omit [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedConditionedPairing_summable {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (hF : giantSignedConditionedEnergy PS ν F ≠ ∞)
    (hG : giantSignedConditionedEnergy PS ν G ≠ ∞) :
    Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i) :=
  giantSignedWeightedPairing_summable_of_energy (giantSignedConditionedWeight PS ν)
    (giantSignedConditionedWeight_nonneg PS ν hν) _ _ hF hG

omit [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedConditionedPairing_energy {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (hF : giantSignedConditionedEnergy PS ν F ≠ ∞)
    (hG : giantSignedConditionedEnergy PS ν G ≠ ∞) :
    ENNReal.ofReal (‖giantSignedConditionedPairing PS ν F G‖ ^ 2) ≤
      giantSignedConditionedEnergy PS ν F * giantSignedConditionedEnergy PS ν G :=
  giantSignedWeightedPairing_energy (giantSignedConditionedWeight PS ν)
    (giantSignedConditionedWeight_nonneg PS ν hν) _ _ hF hG

end
end ArtinMatthews
