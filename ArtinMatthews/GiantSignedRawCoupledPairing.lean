module

public import ArtinMatthews.GiantSignedRawCoupledRow
public import ArtinMatthews.GiantSignedEdgePairingReal


set_option backward.privateInPublic true
@[expose] public section

/-! The original state law disintegrates the coupled row over actual outer choices. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawSmallHaar_nonneg
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) :
    0 ≤ giantTwoSidedResidueHaarStateMass PS M := by
  unfold giantTwoSidedResidueHaarStateMass markedPhysicalMass
  exact div_nonneg
    (Finset.prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hVS j).le) _)
    (Nat.cast_nonneg _)

theorem giantSignedRawStateMass_nonneg
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (s : GiantSignedState PS PB M) :
    0 ≤ giantSignedStateMass PS ν s := by
  unfold giantSignedStateMass
  exact mul_nonneg
    (mul_nonneg (giantSignedRawSmallHaar_nonneg hVS)
      (Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun i _ => hν j _))
    (giantSignedMemoryMass_nonneg ν hν s.2.2)

theorem giantSignedRawCoupledFiberTest_nonneg
    (F : GiantSignedRawCoupledTest PS PB C ell) (hF : ∀ X Y s t, 0 ≤ F X Y s t)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (x z : GiantTwoSidedResidueState PS (k+ell)) (D : ℕ)
    (inflate : GiantSignedPrimeTuple PB (fun j => ell + (C j).card) →
      MarkedPhysicalMarking PB (k+ell)) :
    ∀ X Y a b old out, 0 ≤ giantSignedRawCoupledFiberTest F i x z D inflate X Y a b old out := by
  intro X Y a b old out
  unfold giantSignedRawCoupledFiberTest
  split_ifs
  · exact hF _ _ _ _
  · exact le_rfl

theorem giantSignedRawCoupledSection_nonneg
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g)
    (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (F : GiantSignedRawCoupledTest PS PB C ell) (hF : ∀ X Y s t, 0 ≤ F X Y s t)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell)
    (x : GiantTwoSidedResidueState PS (k+ell))
    (a : MarkedPhysicalMarking PB (k+ell)) (m : GiantSignedMemory PB) :
    0 ≤ giantSignedRawCoupledSection ν V κ q ρ F i x a m := by
  unfold giantSignedRawCoupledSection
  apply Finset.sum_nonneg
  intro z _
  exact mul_nonneg (giantSignedSmallEdgeWeight_nonneg _ _ _ _ _)
    (giantSignedEdgeCoupledApply_nonneg ν hν V (fun j => (hV j).le) hρ _ _
      (giantSignedRawCoupledFiberTest_nonneg F hF i x z _ _) _ _)

def giantSignedRawCoupledPairing (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (F : GiantSignedRawCoupledTest PS PB C ell) : ℝ≥0∞ :=
  ∑' s : GiantSignedState PS PB (k+ell),
    ENNReal.ofReal (giantSignedStateMass PS ν s * giantSignedRawCoupledRow ν V κ q ρ F s)

def giantSignedRawCoupledSectionPairing (ν : ∀ g, PB g → ℝ) (V : B → ℝ)
    (κ : ℤ) (q ρ : ℝ) (F : GiantSignedRawCoupledTest PS PB C ell)
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) : ℝ≥0∞ :=
  ∑' s : GiantSignedState PS PB (k+ell),
    ENNReal.ofReal (giantSignedStateMass PS ν s *
      giantSignedRawCoupledSection ν V κ q ρ F i s.1 s.2.1 s.2.2)

theorem giantSignedRawCoupledPairing_outer
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (hV : ∀ g, 0 < V g) (κ : ℤ) (q : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (F : GiantSignedRawCoupledTest PS PB C ell) (hF : ∀ X Y s t, 0 ≤ F X Y s t) :
    giantSignedRawCoupledPairing ν V κ q ρ F =
      ∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, ENNReal.ofReal (giantSignedRawOuterWeight i) *
        giantSignedRawCoupledSectionPairing ν V κ q ρ F i := by
  let I := GiantSignedRawOuterChoice (S := S) PB C ell
  let A := GiantSignedState PS PB (k+ell)
  let w : I → ℝ := giantSignedRawOuterWeight
  let mass : A → ℝ := giantSignedStateMass PS ν
  let p (i : I) := giantSignedStatePermute PS (PB := PB) i.1.1 i.1.2
  let H (i : I) (s : A) := giantSignedRawCoupledSection ν V κ q ρ F i s.1 s.2.1 s.2.2
  have hw (i : I) : 0 ≤ w i := giantSignedRawOuterWeight_nonneg hVB i
  have hm (s : A) : 0 ≤ mass s := giantSignedRawStateMass_nonneg hVS ν hν s
  have hH (i : I) (s : A) : 0 ≤ H i s :=
    giantSignedRawCoupledSection_nonneg ν hν V hV κ q hρ F hF i s.1 s.2.1 s.2.2
  have hpoint (s : A) :
      ENNReal.ofReal (mass s * giantSignedRawCoupledRow ν V κ q ρ F s) =
        ∑ i : I, ENNReal.ofReal (w i) * ENNReal.ofReal (mass s * H i (p i s)) := by
    rw [giantSignedRawCoupledRow_average ν hν V hV κ q hρ F s]
    change ENNReal.ofReal (mass s * ∑ i : I, w i * H i (p i s)) = _
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg (hm s) (mul_nonneg (hw i) (hH i (p i s))))]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_left_comm, ENNReal.ofReal_mul (hw i)]
  unfold giantSignedRawCoupledPairing
  calc
    _ = ∑' s : A, ∑ i : I, ENNReal.ofReal (w i) * ENNReal.ofReal (mass s * H i (p i s)) :=
      tsum_congr hpoint
    _ = ∑ i : I, ∑' s : A, ENNReal.ofReal (w i) * ENNReal.ofReal (mass s * H i (p i s)) := by
      simpa only [tsum_fintype] using (ENNReal.tsum_comm
        (f := fun s : A => fun i : I => ENNReal.ofReal (w i) * ENNReal.ofReal (mass s * H i (p i s))))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.tsum_mul_left]
      congr 1
      change (∑' s : A, ENNReal.ofReal (mass s * H i (p i s))) =
        ∑' s : A, ENNReal.ofReal (mass s * H i s)
      have he := (p i).tsum_eq (fun s : A => ENNReal.ofReal (mass s * H i s))
      simpa only [mass, p, giantSignedStateMass_slot_permute] using he

end
end ArtinMatthews
