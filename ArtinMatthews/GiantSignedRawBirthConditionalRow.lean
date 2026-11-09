module

public import ArtinMatthews.GiantSignedRawConditionalRow
public import ArtinMatthews.GiantSignedRawFreshBirthMass


set_option backward.privateInPublic true
@[expose] public section

/-! Every dependent performed birth in the actual raw edge contributes
its single-point tilted prime factor to the weighted row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]
    {C : B → Finset (Fin k)}

theorem giantSignedRawEdgeBirthConditionalMass_row_bound {n H : ℕ}
    (hPS : ∀ j p, p ∈ PS j → p.Prime) (hPB : ∀ j p, p ∈ PB j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j)) (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    {vmin massMax q ρ v BS W Δ : ℝ}
    (hvmin : 0 < vmin) (hV : ∀ g, vmin ≤ V g) (hMass : 1 ≤ massMax)
    (hq : 0 < q) (hq1 : q ≤ 1) (hBS : 0 ≤ BS)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ)/2) ≤ BS)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v)
    (hW : 0 ≤ W) (hΔ : 0 ≤ Δ) (budget : ℕ) (hC : ∀ g, (C g).card ≤ budget)
    (κ : ℤ) (θ ζ : ℝ) (K : GiantTwoSidedPatternCoefficient PB C ell)
    (hK : ∀ a b aux, ‖K a b aux‖ ≤ W)
    (s : GiantSignedState PS PB (k+ell))
    (hatom : ∀ g p, ν g p ≤ Δ) (hνmass : ∀ g, (∑ p : PB g, ν g p) ≤ massMax)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) (i : Fin n)
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes)
    (hold : ∀ a, giantSignedUniformBirthOperation (k+ell) n H a = .edge i → old a = none) :
    giantSignedRawEdgeConditionalMass ν V κ q ρ θ ζ K s
      (fun c => giantSignedRawFreshBirthGate hPB σ i C c.2.1 old)
      (fun m => v^(∑ g, m.1 g)) ≤
      (W * Δ^(giantSignedUniformBirthStageNonpivots σ (.edge i)).card) *
        (v^(∑ g, s.2.2.1 g) *
          (giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax (ell+budget)) ^ Fintype.card B *
          BS ^ Fintype.card S) :=
  giantSignedRawEdgeConditionalMass_row_bound hPS hPB hdis hVS hVB ν hν V
    hvmin hV hMass hq hq1 hBS hbudget hρ hρ1 hv hW (pow_nonneg hΔ _) budget hC
    κ θ ζ K hK s (fun c => giantSignedRawFreshBirthGate hPB σ i C c.2.1 old)
    (fun c => giantSignedRawFreshBirthGate_mass hPB ν hν hΔ hMass hatom hνmass σ i C c.2.1 old hold)

end
end ArtinMatthews
