module

public import ArtinMatthews.GiantSignedDoubledWordEnergy
public import ArtinMatthews.GiantSignedDoubledBoundaryNorm
public import ArtinMatthews.GiantSignedRawAbsoluteSymmetry
public import ArtinMatthews.GiantSignedBoundaryDomain


set_option backward.privateInPublic true
@[expose] public section

/-! The literal doubled positive source boundary has the norm budget
used for removing the memory cutoff. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem giantSignedSourceDoubledBoundary_norm_exists
    {q ρ vmin vmax C₀ : ℝ} (ell : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hgap : Real.sqrt q < ρ ^ 2) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax) :
    ∃ v BS : ℝ, 1 < v ∧ 0 ≤ BS ∧
      (∀ (n : ℕ) (i : Fin (n+1)) (Vg : ℝ), 0 ≤ Vg → Vg ≤ vmax →
        |giantSignedSourceVisitQ q n i / ρ ^ 2| +
          |-(1-giantSignedSourceVisitQ q n i) / ρ| / v < 1 ∧
        |giantSignedSourceVisitQ q n i / ρ ^ 2| +
          2 * |-(1-giantSignedSourceVisitQ q n i) * Vg / ρ| / v < 1) ∧
      ∀ (S B I : Type u) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
        (PS : S → Finset ℕ) (PB : B → Finset ℕ)
        [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
        [∀ g, ∀ p : PB g, NeZero p.val]
        (k n budget : ℕ) (ν : ∀ g, PB g → ℝ),
        (∀ g p, 0 ≤ ν g p) → (∀ g, (∑ p : PB g, ν g p) ≤ 2) →
        (∀ j p, p ∈ PS j → p.Prime) → (∀ j p, p ∈ PB j → p.Prime) →
        Pairwise (fun i j => Disjoint (PS i) (PS j)) →
        (∀ j, vmin ≤ bandReciprocalMass (PS j)) →
        (∀ g, vmin ≤ bandReciprocalMass (PB g)) →
        (∀ g, bandReciprocalMass (PB g) ≤ vmax) →
      ∀ (L C₁ W : ℝ), 0 < L → 0 ≤ W →
        (Fintype.card S : ℝ) ≤ C₀ * Real.log L → (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
      ∀ (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k)),
        (∀ i p, p ∈ patterns i → ∀ g, (C i p g).card ≤ budget) →
        (∀ i, ((patterns i).card : ℝ) * W ≤ L ^ C₁) →
      ∀ (κ : Fin n → ℤ) (θ : ℝ) (ζ : Fin n → ℝ)
        (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell),
        (∀ i p, p ∈ patterns i → ∀ a b aux, ‖K i p a b aux‖ ≤ W) →
        giantSignedStateEnergy PS ν (giantSignedBoundary (M := k+ell)) ≤ 2 →
        let V := fun g => bandReciprocalMass (PB g)
        let η (i : Fin n) (p : I) (s : GiantSignedState PS PB (k+ell))
            (r : GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2) :=
          giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i p) (fun _ _ => 1) s r
        ‖giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ
          n patterns C κ (giantSignedSourceVisitQ q n) ζ K η‖ ≤
          2 * (L ^ (giantSignedSourceVisitExponent C₀ (2*vmax) ρ v / 2)) ^ (n+1) *
            (L ^ giantSignedSourceAbsoluteExponent C₀ C₁ BS ρ v vmin vmax 2 (ell+budget)) ^ n := by
  obtain ⟨v, hv, hweights⟩ := giantSignedSourceVisitWeights_exists hq.le hq1.le hρ hgap vmax
  obtain ⟨BS, hBS, hsmall⟩ := giantSignedSmallRowBudget_exists hq hq1 hvmin ell
  refine ⟨v, BS, hv, hBS, hweights, ?_⟩
  intro S B I _ _ _ _ PS PB _ _ k n budget ν hν hMass hPS hPB hdis hVsmall hVmin hVmax
    L C₁ W hL hW hS hB patterns C hC hcost κ θ ζ K hK hboundary
  let V := fun g => bandReciprocalMass (PB g)
  let η (i : Fin n) (p : I) (s : GiantSignedState PS PB (k+ell))
      (r : GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2) :=
    giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i p) (fun _ _ => 1) s r
  let visitQ := giantSignedSourceVisitQ q n
  have hVS (j : S) : 0 < bandReciprocalMass (PS j) := hvmin.trans_le (hVsmall j)
  have hVB (g : B) : 0 < V g := hvmin.trans_le (hVmin g)
  have hsqrt : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
  have hqi (i : Fin (n+1)) : 0 ≤ visitQ i ∧ visitQ i ≤ 1 :=
    ⟨(giantSignedSourceVisitQ_bounds hq.le hq1.le n i).1,
      (giantSignedSourceVisitQ_bounds hq.le hq1.le n i).2.trans hsqrt⟩
  have hrow (i : Fin (n+1)) : |visitQ i / ρ ^ 2| + |-(1-visitQ i) / ρ| / v ≤ 1 :=
    (hweights n i 0 le_rfl hvmax).1.le
  have hcol (i : Fin (n+1)) (g : B) :
      |visitQ i / ρ ^ 2| + 2 * |-(1-visitQ i) * V g / ρ| / v ≤ 1 :=
    (hweights n i (V g) (hVB g).le (hVmax g)).2.le
  have hη (i : Fin n) (p : I) (_ : p ∈ patterns i) (s : GiantSignedState PS PB (k+ell))
      (r : GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2) : ‖η i p s r‖ ≤ 1 :=
    giantSignedRawEdgeAbsoluteMultiplier_norm_le ν V (κ i) q ρ θ (ζ i) (K i p)
      (fun _ _ => 1) s r (by simp)
  have hηeq (i : Fin n) (p : I) (_ : p ∈ patterns i) (s : GiantSignedState PS PB (k+ell))
      (σ : ∀ g, Equiv.Perm (Fin (s.2.2.1 g)))
      (r : GiantSignedRawEdgeMove PS PB ell (C i p) (giantSignedMemoryPermute s.2.2 σ)) :
      η i p (s.1,s.2.1,giantSignedMemoryPermute s.2.2 σ) r =
        η i p s (giantSignedRawEdgeOldEquiv s.2.2 σ r) :=
    giantSignedRawEdgeAbsoluteMultiplier_old_permute ν V (κ i) q ρ θ (ζ i) (K i p)
      (fun _ _ => 1) s σ r rfl
  have hw := (giantSignedDoubledChronologicalWord_energy hPS hPB hdis hVS hVB ν hν V
    hvmin hvmax hVmin hVmax hMass hq hq1.le hBS (fun j z => hsmall _ (hVsmall j) z)
    hρ hρ1 hv.le hW hL hS hB budget θ giantSignedBoundary giantSignedBoundary_exponential
    (fun s a => giantSignedBoundary_memorySymmetric s a) n patterns C hC hcost κ visitQ ζ
    hqi hrow hcol K hK η hη hηeq).2.2
  let Cv := giantSignedSourceVisitExponent C₀ (2*vmax) ρ v / 2
  let Cₐ := giantSignedSourceAbsoluteExponent C₀ C₁ BS ρ v vmin vmax 2 (ell+budget)
  have hpow (a : ℝ) : L ^ (2*a) = (L ^ a) ^ (2 : ℕ) := by
    calc
      _ = L ^ (a * (2 : ℕ)) := by congr 1; norm_num; ring
      _ = _ := Real.rpow_mul_natCast hL.le a 2
  have hCv : 2 * Cv = giantSignedSourceVisitExponent C₀ (2*vmax) ρ v := by dsimp [Cv]; ring
  have hpowCv := hpow Cv
  rw [hCv] at hpowCv
  have hpowCa : L ^ (2 * giantSignedSourceAbsoluteExponent C₀ C₁ BS ρ v vmin vmax 2
      (ell+budget)) = (L ^ Cₐ) ^ (2 : ℕ) := hpow Cₐ
  exact giantSignedDoubledBoundaryPairing_norm_of_energy PS ν hν hVS V q ρ θ L Cv Cₐ hL
    n patterns C κ visitQ ζ K η hboundary (by simpa only [hpowCv, hpowCa] using hw)

end
end ArtinMatthews
