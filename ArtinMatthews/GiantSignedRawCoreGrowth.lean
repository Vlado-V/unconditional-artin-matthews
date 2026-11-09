module

public import ArtinMatthews.GiantSignedRawCoreData


set_option backward.privateInPublic true
@[expose] public section

/-! The original canonical raw core preserves a single exponential
degree bound uniformly over its small state and active labels. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawCoreApply_row_bound
    (hPS : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ U u BS : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (aux : GiantTwoSidedPatternAuxiliary PB C)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (s : GiantSignedState PS PB (k+ell)) :
    ‖giantSignedRawCoreApply ν V κ q ρ aux f s‖ ≤
      U * u ^ (∑ g, s.2.2.1 g) *
        (giantSignedEdgeUniformConstant ρ u vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S := by
  unfold giantSignedRawCoreApply
  exact giantSignedSmallFreeEdgeApply_row_bound hPS hdis hVS ν hν V hvmin hV hMass
    hq hq1 hBS hbudget hρ hρ1 hU hu (ell+budget)
    (fun g => Nat.add_le_add_left (hC g) ell) κ
    (giantTwoSidedPatternCopiedProduct C s.2.1 * giantTwoSidedPatternAuxiliaryProduct aux)
    (fun z a m => f (z, giantSignedPatternFill C s.2.1 a, m))
    (fun z a m => hf (z, giantSignedPatternFill C s.2.1 a, m))
    s.1 (giantSignedPatternFreeLabels C s.2.1) s.2.2

end
end ArtinMatthews
