module

public import ArtinMatthews.GiantSignedRawCoreData
public import ArtinMatthews.GiantSignedSmallFreeEdge


set_option backward.privateInPublic true
@[expose] public section

/-! Energy of the full canonical core under its original copied law. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawCoreApply_energy
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U u BS : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (aux : GiantTwoSidedPatternAuxiliary PB C)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedRawCoreApply ν V κ q ρ aux f) ≤
      ENNReal.ofReal ((BS ^ Fintype.card S) ^ 2 *
        (giantSignedEdgeEnergyConstant ρ v vmin vmax massMax (ell+budget)) ^ Fintype.card B) *
          giantSignedStateEnergy PS ν f := by
  rw [giantSignedStateEnergy_copiedFree PS hVS ν hν C,
    giantSignedStateEnergy_copiedFree PS hVS ν hν C]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have he := giantSignedSmallFreeEdgeApply_energy hPS hdis hVS ν hν V
    hvmin hVmin hVmax hMass hq hq1 hBS hbudget hρ hρ1 hv hU hu
    (ell+budget) (fun g => Nat.add_le_add_left (hC g) ell) κ
    (giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct aux)
    (fun s a m => f (s, giantSignedPatternSourceFill C c a, m))
    (fun s a m => hf (s, giantSignedPatternSourceFill C c a, m))
    (fun s a => hsym s (giantSignedPatternSourceFill C c a))
  have hfun : (fun s a m => giantSignedRawCoreApply ν V κ q ρ aux f
      (s, giantSignedPatternSourceFill C c a, m)) =
      giantSignedSmallFreeEdgeApply ν V κ q ρ
        (giantSignedCopiedLabelsProduct c * giantTwoSidedPatternAuxiliaryProduct aux)
        (fun z b out => f (z, giantSignedPatternSourceFill C c b, out)) := by
    funext s a m
    exact giantSignedRawCoreApply_sourceFill ν V κ q ρ aux f c s a m
  rw [hfun]
  exact (mul_le_mul_right he (ENNReal.ofReal (giantSignedPatternCopiedMass ν c))).trans_eq (by ac_rfl)

end
end ArtinMatthews
