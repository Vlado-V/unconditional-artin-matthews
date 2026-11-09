module

public import ArtinMatthews.GiantSignedCleanDamping
public import ArtinMatthews.GiantSignedResidueFiber
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


set_option backward.privateInPublic true
@[expose] public section

/-! The clean residue estimate is summed over every pending degree and
prime list with the original factorial weights. No degree restriction is imposed. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

abbrev GiantSignedMemorySectors {B : Type*} (P : B → Finset ℕ) :=
  Σ degree : B → ℕ, GiantSignedPrimeLists P degree

def giantSignedMemoryAt {B : Type*} {P : B → Finset ℕ}
    (s : GiantSignedMemorySectors P) (r : GiantSignedResidues s.2) : GiantSignedMemory P :=
  (giantSignedMemoryCoordinates P).symm ⟨s.1, s.2, r⟩

theorem giantSignedMemoryAt_mass {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (s : GiantSignedMemorySectors P) (r : GiantSignedResidues s.2) :
    giantSignedMemoryMass ν (giantSignedMemoryAt s r) = giantSignedPrimeListMass ν s.2 := rfl

theorem giantSignedMemoryAt_translate {B : Type*} {P : B → Finset ℕ}
    (s : GiantSignedMemorySectors P) (r : GiantSignedResidues s.2) (d : ℤ) :
    giantSignedMemoryTranslate d (giantSignedMemoryAt s r) =
      giantSignedMemoryAt s (giantSignedResidueTranslate s.2 d r) := rfl

def giantSignedSmallHaar {S : Type*} [Fintype S] (PS : S → Finset ℕ) : ℝ :=
  ((∏ p ∈ markedPhysicalBandPrimes PS, p : ℕ) : ℝ)⁻¹

theorem giantSignedSmallHaar_nonneg {S : Type*} [Fintype S] (PS : S → Finset ℕ) :
    0 ≤ giantSignedSmallHaar PS := inv_nonneg.mpr (Nat.cast_nonneg _)

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
  (PS : S → Finset ℕ) {PB : B → Finset ℕ}
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
  [∀ (g : B) (p : PB g), NeZero p.val]

abbrev GiantSignedSectorFunctions (M : ℕ) :=
  (s : GiantSignedMemorySectors PB) →
    GiantSignedResidueFiber PS s.2 → MarkedPhysicalMarking PB M → ℂ

def giantSignedSectorEnergy {M : ℕ}
    (ν : ∀ g, PB g → ℝ) (f : GiantSignedSectorFunctions PS (PB := PB) M) : ℝ≥0∞ :=
  ∑' s : GiantSignedMemorySectors PB,
    ENNReal.ofReal (giantSignedSmallHaar PS * giantSignedPrimeListMass ν s.2 *
      ∑ x : GiantSignedResidueFiber PS s.2, ∑ a,
        giantSignedActiveMass ν a * ‖f s x a‖ ^ 2)

def giantSignedSectorPendingDamping (ρ : ℝ) (s : GiantSignedMemorySectors PB)
    (x : GiantSignedResidueFiber PS s.2) : ℂ :=
  giantSignedPendingDamping ρ (giantSignedMemoryAt s x.2)

def giantSignedUnboundedCleanApply {I : Type*} {k ell : ℕ}
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (Θ ζ ρ : ℝ)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℤ)
    (f : GiantSignedSectorFunctions PS (PB := PB) (k+ell)) :
    GiantSignedSectorFunctions PS (PB := PB) (k+ell) :=
  fun s => giantSignedDampedCleanFiberApply freshLaw auxLaw patterns C Θ ζ K
    (giantSignedResidueDiagonal PS s.2 d)
    (giantSignedSectorPendingDamping PS ρ s) (giantSignedSectorPendingDamping PS ρ s) (f s)

theorem giantSignedUnboundedCleanApply_energy {I : Type*} {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (freshLaw auxLaw : ∀ g, PB g → ℝ) (patterns : Finset I)
    (C : I → B → Finset (Fin k)) (Θ ζ ρ U : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (K : ∀ v, GiantTwoSidedPatternCoefficient PB (C v) ell) (d : ℤ)
    (hIdeal : ∀ θ (h : MarkedPhysicalMarking PB (k+ell) → ℂ), IdealSymmetric h →
      (∑ a, giantSignedActiveMass ν a *
        ‖idealOperatorWithLaws freshLaw auxLaw patterns C θ ζ K h a‖ ^ 2) ≤
          U ^ 2 * ∑ a, giantSignedActiveMass ν a * ‖h a‖ ^ 2)
    (f : GiantSignedSectorFunctions PS (PB := PB) (k+ell))
    (hf : ∀ s x, IdealSymmetric (f s x)) :
    giantSignedSectorEnergy PS ν
        (giantSignedUnboundedCleanApply PS freshLaw auxLaw patterns C Θ ζ ρ K d f) ≤
      ENNReal.ofReal (U ^ 2) * giantSignedSectorEnergy PS ν f := by
  classical
  unfold giantSignedSectorEnergy
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  have hmass : 0 ≤ giantSignedSmallHaar PS * giantSignedPrimeListMass ν s.2 := by
    apply mul_nonneg (giantSignedSmallHaar_nonneg PS)
    exact giantSignedMemoryMass_nonneg ν hν (giantSignedMemoryAt s 0)
  have hactive (a : MarkedPhysicalMarking PB (k+ell)) : 0 ≤ giantSignedActiveMass ν a :=
    Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g (a g i)
  have hd (x : GiantSignedResidueFiber PS s.2) :
      ‖giantSignedSectorPendingDamping PS ρ s x‖ ≤ 1 :=
    giantSignedPendingDamping_norm hρ hρ1 _
  have he := giantSignedDampedCleanFiberApply_energy
    (giantSignedActiveMass ν) hactive freshLaw auxLaw patterns C Θ ζ U K
    (giantSignedResidueDiagonal PS s.2 d)
    (giantSignedSectorPendingDamping PS ρ s) (giantSignedSectorPendingDamping PS ρ s)
    hd hd hIdeal (f s) (hf s)
  change ENNReal.ofReal (_ * _) ≤ _
  calc
    _ ≤ ENNReal.ofReal ((giantSignedSmallHaar PS * giantSignedPrimeListMass ν s.2) *
        (U ^ 2 * ∑ x : GiantSignedResidueFiber PS s.2, ∑ a,
          giantSignedActiveMass ν a * ‖f s x a‖ ^ 2)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he hmass)
    _ = _ := by
      rw [mul_left_comm _ (U ^ 2), ENNReal.ofReal_mul (sq_nonneg U)]

end
end ArtinMatthews
