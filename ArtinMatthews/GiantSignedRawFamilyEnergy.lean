module

public import ArtinMatthews.GiantSignedRawEdgeEnergy
public import ArtinMatthews.GiantSignedStateFiniteSumEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The full finite raw family retains every pattern and the exact
original endpoint and auxiliary averages. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedRawEdgeFamilyApply_energy {I : Type*}
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U u BS W : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (hW : 0 ≤ W) (budget : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ i ∈ patterns, ∀ g, (C i g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ W)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ s r, ‖η i s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f) ≤
      ENNReal.ofReal (giantSignedRawEdgeEnergyConstant ((patterns.card : ℝ) * W) BS
        (Fintype.card S) (Fintype.card B) ρ v vmin vmax massMax (ell+budget)) *
          giantSignedStateEnergy PS ν f := by
  classical
  let F (i : ↥patterns) : GiantSignedState PS PB (k+ell) → ℂ :=
    giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i.val) (η i.val) f
  let E := giantSignedRawEdgeEnergyConstant W BS (Fintype.card S) (Fintype.card B)
    ρ v vmin vmax massMax (ell+budget)
  have hi (i : ↥patterns) : giantSignedStateEnergy PS ν (F i) ≤
      ENNReal.ofReal E * giantSignedStateEnergy PS ν f :=
    giantSignedRawEdgeApply_energy hPS hPB hdis hVS hVB ν hν V hvmin hVmin hVmax hMass
      hq hq1 hBS hbudget hρ hρ1 hv hU hu hW budget (hC i.val i.property) κ θ ζ
      (K i.val) (hK i.val i.property) (η i.val) (hη i.val i.property) f hf hsym
  have he := giantSignedStateEnergy_sum_le_card_sq PS hVS ν hν F
    (ENNReal.ofReal E * giantSignedStateEnergy PS ν f) hi
  have hsum : (fun s => ∑ i : ↥patterns, F i s) =
      giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K η f := by
    funext s
    let value (i : I) : ℂ := giantSignedRawEdgeApply ν V κ q ρ θ ζ (K i) (η i) f s
    change (∑ i : ↥patterns, value i.val) = ∑ i ∈ patterns, value i
    exact Finset.sum_coe_sort patterns value
  rw [hsum] at he
  have hcard : (Fintype.card ↥patterns : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal ((patterns.card : ℝ) ^ 2) := by
    simp only [Fintype.card_coe, pow_two, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  rw [hcard] at he
  have hconst : (patterns.card : ℝ) ^ 2 * E =
      giantSignedRawEdgeEnergyConstant ((patterns.card : ℝ) * W) BS
        (Fintype.card S) (Fintype.card B) ρ v vmin vmax massMax (ell+budget) := by
    dsimp [E, giantSignedRawEdgeEnergyConstant]
    ring
  exact he.trans_eq (by rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), hconst])

theorem giantSignedRawEdgeFamilyApply_dirty_energy {I : Type*}
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (hVB : ∀ j, 0 < bandReciprocalMass (PB j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin vmax massMax q ρ v U u BS W : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ g, vmin ≤ V g) (hVmax : ∀ g, V g ≤ vmax)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hU : 0 ≤ U) (hu : 1 ≤ u)
    (hW : 0 ≤ W) (budget : ℕ) (patterns : Finset I) (C : I → B → Finset (Fin k))
    (hC : ∀ i ∈ patterns, ∀ g, (C i g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : ∀ i, GiantTwoSidedPatternCoefficient PB (C i) ell)
    (hK : ∀ i ∈ patterns, ∀ a b aux, ‖K i a b aux‖ ≤ W)
    (η : (i : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i) s.2.2 → ℂ)
    (hη : ∀ i ∈ patterns, ∀ s r, ‖η i s r‖ ≤ 1)
    (f : GiantSignedState PS PB (k+ell) → ℂ)
    (hf : ∀ s, ‖f s‖ ≤ U * u ^ (∑ g, s.2.2.1 g))
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedRawEdgeFamilyApply ν V patterns C κ q ρ θ ζ K
      (fun i s r => η i s r * giantSignedRawEdgeDirtyMultiplier s r) f) ≤
      ENNReal.ofReal (giantSignedRawEdgeEnergyConstant ((patterns.card : ℝ) * W) BS
        (Fintype.card S) (Fintype.card B) ρ v vmin vmax massMax (ell+budget)) *
          giantSignedStateEnergy PS ν f := by
  apply giantSignedRawEdgeFamilyApply_energy hPS hPB hdis hVS hVB ν hν V
    hvmin hVmin hVmax hMass hq hq1 hBS hbudget hρ hρ1 hv hU hu hW budget patterns C hC
    κ θ ζ K hK (fun i s r => η i s r * giantSignedRawEdgeDirtyMultiplier s r) _ f hf hsym
  intro i hi s r
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (hη i hi s r) (giantSignedRawEdgeDirtyMultiplier_norm s r)
    (norm_nonneg _) zero_le_one

end
end ArtinMatthews
