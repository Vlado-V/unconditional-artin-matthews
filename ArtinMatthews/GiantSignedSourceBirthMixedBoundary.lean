module

public import ArtinMatthews.GiantSignedBirthMixedBoundary
public import ArtinMatthews.GiantSignedSourceBirthVisit
public import ArtinMatthews.GiantSignedSourceOmissionGain


set_option backward.privateInPublic true
@[expose] public section

/-! The source mixed word uses the literal square-memory cap, visit
schedule and birth-phased operators. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedSourceProjectedBirthBoundary_norm_of_edges
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    {q ρ L C₀ vmax v G Ca : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hρ : 0 < ρ) (hv : 0 < v) (hL1 : 1 ≤ L)
    (hG : 0 ≤ G) (hCa : 0 ≤ Ca) (hvmax : 0 ≤ vmax)
    (hV0 : ∀ g, 0 ≤ bandReciprocalMass (PB g))
    (hVmax : ∀ g, bandReciprocalMass (PB g) ≤ vmax)
    (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (n : ℕ) (θ : ℝ) (patterns : Fin n → Finset I)
    (C : Fin n → I → B → Finset (Fin k)) (κ : Fin n → ℤ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (η : (i : Fin n) → (p : I) → (s : GiantSignedState PS PB (k+ell)) →
      GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2 → ℂ)
    (φ : Fin (n+1) → GiantSignedGhostBirthMultiplier PB) (hφ : ∀ i b p, ‖φ i b p‖ ≤ 1)
    (φ₀ : MarkedPhysicalMarking PB (k+ell) → ℂ) (hφ₀ : ∀ x, ‖φ₀ x‖ ≤ 1)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n (giantSignedSourceMemoryLimit L)))
    (hr : 2 * giantSignedUniformBirthRank σ ≤ n)
    (hηeq : ∀ i p, p ∈ patterns i → ∀ (s : GiantSignedState PS PB (k+ell))
      (τ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
      (r : GiantSignedRawEdgeMove PS PB ell (C i p) (giantSignedMemoryPermute s.2.2 τ)),
      η i p (s.1,s.2.1,giantSignedMemoryPermute s.2.2 τ) r =
        η i p s (giantSignedRawEdgeOldEquiv s.2.2 τ r))
    (hηone : ∀ i, i ∉ giantSignedUniformBirthModifiedEdges σ →
      ∀ p ∈ patterns i, ∀ s r, η i p s r = 1)
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
      giantSignedStateEnergy PS ν (giantSignedProjectedRawEdgeFamilyApply H ν V
        (patterns i) (C i) (κ i) q ρ θ (ζ i) (K i) (η i) w) ≤
        ENNReal.ofReal (L^(2*Ca)) * giantSignedStateEnergy PS ν w) →
    let r := giantSignedUniformBirthRank σ
    ‖giantSignedProjectedBirthBoundaryPairing (PS := PS) H ν V q ρ θ
      n patterns C κ visitQ ζ K η φ φ₀‖ ≤
      2*(L^(Cv/2))^(n+1)*(L^(-G))^(n-2*r)*(L^Ca)^(2*r) := by
  dsimp only
  intro hweights hsigned habs
  let V := fun g => bandReciprocalMass (PB g)
  let H := giantSignedSourceMemoryLimit L
  let visitQ := giantSignedSourceVisitQ q n
  let Cv := giantSignedSourceVisitExponent C₀ vmax ρ v
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hsq (a : ℝ) : (L^a)^2 = L^(2*a) := by
    rw [← Real.rpow_mul_natCast hL.le]
    congr 1
    norm_num
    ring
  have hg : 0 ≤ L^(Cv/2) := Real.rpow_nonneg hL.le _
  have ha : 0 ≤ L^(-G) := Real.rpow_nonneg hL.le _
  have ha1 : L^(-G) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr hG)
  have hb : 1 ≤ L^Ca := Real.one_le_rpow hL1 hCa
  refine giantSignedProjectedBirthBoundaryPairing_norm_of_mixed_local PS H ν hν hVS V
    q ρ θ (L^(Cv/2)) (L^(-G)) (L^Ca) hg ha ha1 hb n patterns C κ visitQ ζ K η φ φ₀ hφ₀ σ hr
    hηeq hηone hboundary ?_ hsigned ?_
  · intro i w hw
    have hsqrt : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
    have hqi := giantSignedSourceVisitQ_bounds hq0 hq1 n i
    have he := giantSignedProjectedBirthVisit_energy_of_source_weights PS H ν hν hMass V hvmax
      hV0 hVmax hVS hρ hv hqi.1 (hqi.2.trans hsqrt) hL hgroups
      (hweights i 0 le_rfl hvmax).1.le (fun g => (hweights i (V g) (hV0 g) (hVmax g)).2.le)
      (φ i) (hφ i) w hw
    have hCv : 2*(Cv/2) = Cv := by ring
    rw [hsq (Cv/2), hCv]
    exact he
  · intro i w hw
    rw [hsq Ca]
    exact habs i w hw

end
end ArtinMatthews
