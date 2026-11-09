module

public import ArtinMatthews.GiantSignedPatternSourceFibers
public import ArtinMatthews.GiantSignedStatePermutationEnergy
public import ArtinMatthews.GiantSignedGhostMemoryCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Exact disintegration of the full original state energy into the
copied-big-label fibers used by the unrestricted free-slot edge. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

def giantSignedCopiedLabelsProduct {B : Type*} [Fintype B] {PB : B → Finset ℕ} {k : ℕ}
    {C : B → Finset (Fin k)} (c : GiantSignedPatternCopiedLabels PB C) : ℕ :=
  ∏ g, ∏ i, (c g i).val

theorem giantSignedPatternSourceFill_product {B : Type*} [Fintype B] {PB : B → Finset ℕ}
    {k ell : ℕ} (C : B → Finset (Fin k)) (c : GiantSignedPatternCopiedLabels PB C)
    (t : GiantSignedPrimeTuple PB (fun g => ell + (C g).card)) :
    giantTwoSidedPatternCopiedProduct C (giantSignedPatternSourceFill C c t) =
      giantSignedCopiedLabelsProduct c := by
  classical
  unfold giantTwoSidedPatternCopiedProduct giantSignedCopiedLabelsProduct
  apply Finset.prod_congr rfl
  intro g _
  rw [Finset.prod_subtype (p := fun i : Fin k => i ∉ C g) (Finset.univ \ C g)
    (by simp) (fun i => (giantSignedPatternSourceFill C c t g (Fin.castAdd ell i)).val)]
  apply Finset.prod_congr rfl
  intro i _
  rw [giantSignedPatternSourceFill_copied]

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

omit [DecidableEq S] [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
private theorem small_haar_nonneg
    (hV : ∀ j, 0 < bandReciprocalMass (PS j)) :
    0 ≤ giantTwoSidedResidueHaarStateMass PS M := by
  unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
  exact div_nonneg
    (Finset.prod_nonneg (fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _))
    (Nat.cast_nonneg _)

theorem giantSignedStateEnergy_memorySlices
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateEnergy PS ν f =
      ∑ s : GiantTwoSidedResidueState PS M, ∑ a : MarkedPhysicalMarking PB M,
        ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a) *
          giantSignedGhostMemoryEnergy ν (fun m => f (s,a,m)) := by
  rw [giantSignedStateEnergy_eq_tsum]
  simp only [ENNReal.tsum_prod']
  have he (s : GiantTwoSidedResidueState PS M) (a : MarkedPhysicalMarking PB M) :
      (∑' m : GiantSignedMemory PB,
        ENNReal.ofReal (giantSignedStateMass PS ν (s,a,m) * ‖f (s,a,m)‖ ^ 2)) =
        ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a) *
          giantSignedGhostMemoryEnergy ν (fun m => f (s,a,m)) := by
    unfold giantSignedGhostMemoryEnergy
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro m
    have hm : 0 ≤ giantTwoSidedResidueHaarStateMass PS M * giantSignedActiveMass ν a :=
      mul_nonneg (small_haar_nonneg PS hV)
        (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g _)))
    rw [← ENNReal.ofReal_mul hm]
    congr 1
    unfold giantSignedStateMass
    ring
  simp_rw [he, tsum_fintype]

def giantSignedFreeStateEnergy {t : B → ℕ}
    (ν : ∀ g, PB g → ℝ)
    (f : GiantTwoSidedResidueState PS M → GiantSignedPrimeTuple PB t →
      GiantSignedMemory PB → ℂ) : ℝ≥0∞ :=
  ∑ s : GiantTwoSidedResidueState PS M, ∑ a : GiantSignedPrimeTuple PB t,
    ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS M * giantSignedFreePrimeRealMass ν a) *
      giantSignedGhostMemoryEnergy ν (f s a)

theorem giantSignedFreeStateEnergy_factor {t : B → ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ)
    (f : GiantTwoSidedResidueState PS M → GiantSignedPrimeTuple PB t →
      GiantSignedMemory PB → ℂ) :
    giantSignedFreeStateEnergy PS ν f =
      ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS M) *
        ∑ s : GiantTwoSidedResidueState PS M, ∑ a : GiantSignedPrimeTuple PB t,
          ENNReal.ofReal (giantSignedFreePrimeRealMass ν a) * giantSignedGhostMemoryEnergy ν (f s a) := by
  unfold giantSignedFreeStateEnergy
  simp only [ENNReal.ofReal_mul (small_haar_nonneg PS hV), Finset.mul_sum, mul_assoc]

theorem giantSignedStateEnergy_copiedFree {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (C : B → Finset (Fin k)) (f : GiantSignedState PS PB (k+ell) → ℂ) :
    giantSignedStateEnergy PS ν f =
      ∑ c : GiantSignedPatternCopiedLabels PB C,
        ENNReal.ofReal (giantSignedPatternCopiedMass ν c) *
          giantSignedFreeStateEnergy PS ν
            (fun s t m => f (s, giantSignedPatternSourceFill C c t, m)) := by
  rw [giantSignedStateEnergy_memorySlices PS hV ν hν]
  have hc (c : GiantSignedPatternCopiedLabels PB C) : 0 ≤ giantSignedPatternCopiedMass ν c :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hν g _))
  have he (s : GiantTwoSidedResidueState PS (k+ell)) :
      (∑ a : MarkedPhysicalMarking PB (k+ell),
        ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a) *
          giantSignedGhostMemoryEnergy ν (fun m => f (s,a,m))) =
        ∑ c : GiantSignedPatternCopiedLabels PB C,
          ENNReal.ofReal (giantSignedPatternCopiedMass ν c) *
            ∑ t : GiantSignedPrimeTuple PB (fun g => ell + (C g).card),
              ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS (k+ell) *
                giantSignedFreePrimeRealMass ν t) *
                giantSignedGhostMemoryEnergy ν
                  (fun m => f (s, giantSignedPatternSourceFill C c t, m)) := by
    calc
      _ = ∑ c : GiantSignedPatternCopiedLabels PB C,
          ∑ t : GiantSignedPrimeTuple PB (fun g => ell + (C g).card),
            ENNReal.ofReal (giantTwoSidedResidueHaarStateMass PS (k+ell) *
              giantSignedActiveMass ν (giantSignedPatternSourceFill C c t)) *
              giantSignedGhostMemoryEnergy ν
                (fun m => f (s, giantSignedPatternSourceFill C c t, m)) := by
        simpa only [Fintype.sum_prod_type, giantSignedPatternSourceEquiv,
          Equiv.coe_fn_symm_mk] using
          ((giantSignedPatternSourceEquiv (P := PB) (ell := ell) C).symm.sum_comp
            (fun a => ENNReal.ofReal
              (giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedActiveMass ν a) *
                giantSignedGhostMemoryEnergy ν (fun m => f (s,a,m)))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [giantSignedPatternSourceFill_mass]
        calc
          _ = ENNReal.ofReal (giantSignedPatternCopiedMass ν c *
              (giantTwoSidedResidueHaarStateMass PS (k+ell) * giantSignedFreePrimeRealMass ν t)) *
              giantSignedGhostMemoryEnergy ν
                (fun m => f (s, giantSignedPatternSourceFill C c t, m)) := by
            congr 2
            ring
          _ = _ := by rw [ENNReal.ofReal_mul (hc c), mul_assoc]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  unfold giantSignedFreeStateEnergy
  rw [Finset.mul_sum]

end
end ArtinMatthews
