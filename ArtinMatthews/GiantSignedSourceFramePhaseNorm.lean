module

public import ArtinMatthews.GiantSignedSourceBirthMixedBoundary
public import ArtinMatthews.GiantSignedLocalBirthPhase


set_option backward.privateInPublic true
@[expose] public section

/-! The literal frame phases are admissible in the actual source mixed
word. Untouched edges retain the full signed estimate. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

variable {S B I : Type u} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n H : ℕ}

theorem giantSignedRawEdgeFramePhase_old_permute {C : B → Finset (Fin k)}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (τ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (i : Fin n) (s : GiantSignedState PS PB (k+ell))
    (π : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
    (r : GiantSignedRawEdgeMove PS PB ell C (giantSignedMemoryPermute s.2.2 π)) :
    giantSignedRawEdgeFramePhase σ τ i (s.1,s.2.1,giantSignedMemoryPermute s.2.2 π) r =
      giantSignedRawEdgeFramePhase σ τ i s (giantSignedRawEdgeOldEquiv s.2.2 π r) :=
  rfl

variable [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ)
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedSourceFramePhaseBoundary_norm
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    {q ρ L C₀ vmax v G Ca : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hρ : 0 < ρ) (hv : 0 < v) (hL1 : 1 ≤ L)
    (hG : 0 ≤ G) (hCa : 0 ≤ Ca) (hvmax : 0 ≤ vmax)
    (hV0 : ∀ g, 0 ≤ bandReciprocalMass (PB g))
    (hVmax : ∀ g, bandReciprocalMass (PB g) ≤ vmax)
    (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (θ : ℝ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n (giantSignedSourceMemoryLimit L)))
    (hr : 2 * giantSignedUniformBirthRank σ ≤ n)
    (τ : GiantSignedUniformBirthAddress B (k+ell) n (giantSignedSourceMemoryLimit L) → AddCircle (1 : ℝ))
    (hboundary : giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2) :
    let V := fun g => bandReciprocalMass (PB g)
    let H := giantSignedSourceMemoryLimit L
    let visitQ := giantSignedSourceVisitQ q n
    let Cv := giantSignedSourceVisitExponent C₀ vmax ρ v
    (∀ (i : Fin (n+1)) (Vg : ℝ), 0 ≤ Vg → Vg ≤ vmax →
      |visitQ i / ρ ^ 2| + |-(1-visitQ i) / ρ| / v < 1 ∧
      |visitQ i / ρ ^ 2| + 2 * |-(1-visitQ i) * Vg / ρ| / v < 1) →
    (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (fun _ _ _ => 1) w) ≤
        ENNReal.ofReal ((L^(-G))^2) * giantSignedStateEnergy PS ν w) →
    (∀ (i : Fin n) (w : GiantSignedState PS PB (k+ell) → ℂ),
      (∀ s a, GiantSignedMemorySymmetric (fun m => w (s,a,m))) →
      ∀ (η : (p : I) → (s : GiantSignedState PS PB (k+ell)) →
        GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ),
        (∀ p ∈ patterns i, ∀ s r, ‖η p s r‖ ≤ 1) →
        giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
          (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) η w) ≤
          ENNReal.ofReal (L^(2*Ca)) * giantSignedStateEnergy PS ν w) →
    let r := giantSignedUniformBirthRank σ
    ‖giantSignedProjectedBirthBoundaryPairing (PS := PS) H ν V q ρ θ
      n patterns C κ visitQ ζ K (fun i _ s r => giantSignedRawEdgeFramePhase σ τ i s r)
      (giantSignedVisitFramePhase σ τ) (giantSignedInitialFramePhase σ τ)‖ ≤
      2*(L^(Cv/2))^(n+1)*(L^(-G))^(n-2*r)*(L^Ca)^(2*r) := by
  dsimp only
  intro hweights hsigned habs
  refine giantSignedSourceProjectedBirthBoundary_norm_of_edges PS ν hν hMass hVS
    hq0 hq1 hρ hv hL1 hG hCa hvmax hV0 hVmax hgroups n θ patterns C κ ζ K
    (fun i _ s r => giantSignedRawEdgeFramePhase σ τ i s r) (giantSignedVisitFramePhase σ τ)
    (fun i _ _ => giantSignedFrameLocalMultiplier_norm_le σ τ (.visit i) _)
    (giantSignedInitialFramePhase σ τ)
    (fun _ => giantSignedFrameLocalMultiplier_norm_le σ τ .initial _) σ hr
    (fun i _ _ s π r => giantSignedRawEdgeFramePhase_old_permute σ τ i s π r)
    (fun i hi _ _ s r => giantSignedRawEdgeFramePhase_unaffected σ τ i s r
      (fun he => hi ((giantSignedUniformBirthModifiedEdges_mem σ i).mpr he)))
    hboundary hweights hsigned ?_
  intro i w hsym
  exact habs i w hsym (fun _ s r => giantSignedRawEdgeFramePhase σ τ i s r)
    (fun _ _ s r => giantSignedRawEdgeFramePhase_norm_le σ τ i s r)

end
end ArtinMatthews
