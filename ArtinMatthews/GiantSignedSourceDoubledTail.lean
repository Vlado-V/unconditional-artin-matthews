module

public import ArtinMatthews.GiantSignedSourceDoubledBoundary
public import ArtinMatthews.GiantSignedSourceMemoryTailBudget
public import ArtinMatthews.GiantSignedSourceTiltedBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! The original doubled positive boundary absorbs the source memory
limit after accounting for every possible store. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

theorem giantSignedSourceDoubledTail_eventually
    {q ρ vmin vmax c C₀ : ℝ} (ell : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hgap : Real.sqrt q < ρ ^ 2) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax)
    (hc : 0 < c) (hC₀ : 0 ≤ C₀) :
    ∃ v BS : ℝ, 1 < v ∧ 0 ≤ BS ∧
      (∀ (n : ℕ) (i : Fin (n+1)) (Vg : ℝ), 0 ≤ Vg → Vg ≤ vmax →
        |giantSignedSourceVisitQ q n i / ρ ^ 2| +
          |-(1-giantSignedSourceVisitQ q n i) / ρ| / v < 1 ∧
        |giantSignedSourceVisitQ q n i / ρ ^ 2| +
          2 * |-(1-giantSignedSourceVisitQ q n i) * Vg / ρ| / v < 1) ∧
      ∀ (k budget : ℕ), 1 ≤ k+ell → ∀ (C₁ A : ℝ), 0 ≤ C₁ → 0 ≤ A →
      ∀ᶠ x : ℝ in atTop,
        ∀ (S B I : Type u) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
          (PS : S → Finset ℕ) (PB : B → Finset ℕ)
          [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
          [∀ g, ∀ p : PB g, NeZero p.val],
          (∀ j p, p ∈ PS j → p.Prime) → (∀ j p, p ∈ PB j → p.Prime) →
          Pairwise (fun i j => Disjoint (PS i) (PS j)) →
          (∀ j, vmin ≤ bandReciprocalMass (PS j)) →
          (∀ g, vmin ≤ bandReciprocalMass (PB g)) →
          (∀ g, bandReciprocalMass (PB g) ≤ vmax) →
          (∀ g (p : PB g), Real.exp ((Real.log x) ^ c) ≤ (p.val : ℝ)) →
          (Fintype.card S : ℝ) ≤ C₀ * Real.log (Real.log x) →
          (Fintype.card B : ℝ) ≤ C₀ * Real.log (Real.log x) →
        let L := Real.log x
        let n := giantTwoSidedSourceMomentLength x
        let visitQ := giantSignedSourceVisitQ q n
        let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
        let V := fun g => bandReciprocalMass (PB g)
        ∀ (W : ℝ), 0 ≤ W →
        ∀ (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k)),
          (∀ i p, p ∈ patterns i → ∀ g, (C i p g).card ≤ budget) →
          (∀ i, ((patterns i).card : ℝ) * W ≤ L ^ C₁) →
        ∀ (κ : Fin n → ℤ) (θ : ℝ) (ζ : Fin n → ℝ)
          (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell),
          (∀ i p, p ∈ patterns i → ∀ a b aux, ‖K i p a b aux‖ ≤ W) →
          let η (i : Fin n) (p : I) (s : GiantSignedState PS PB (k+ell))
              (r : GiantSignedRawEdgeMove PS PB ell (C i p) s.2.2) :=
            giantSignedRawEdgeAbsoluteMultiplier ν V (κ i) q ρ θ (ζ i) (K i p)
              (fun _ _ => 1) s r
          ‖giantSignedDoubledChronologicalBoundaryPairing ν V q ρ θ
            n patterns C κ visitQ ζ K η‖ /
            (2 : ℝ) ^ (giantSignedSourceMemoryLimit L - (ell+budget)*Fintype.card B*n) ≤
            (L ^ (-A)) ^ n := by
  obtain ⟨v, BS, hv, hBS, hweights, hnorm⟩ :=
    giantSignedSourceDoubledBoundary_norm_exists (C₀ := C₀) ell hq hq1 hρ hρ1 hgap hvmin hvmax
  refine ⟨v, BS, hv, hBS, hweights, ?_⟩
  intro k budget hM C₁ A hC₁ hA
  let Cv := giantSignedSourceVisitExponent C₀ (2*vmax) ρ v / 2
  let Cₐ := giantSignedSourceAbsoluteExponent C₀ C₁ BS ρ v vmin vmax 2 (ell+budget)
  have hCv : 0 ≤ Cv := by
    unfold Cv giantSignedSourceVisitExponent
    positivity
  have hCₐ : 0 ≤ Cₐ := by
    unfold Cₐ giantSignedSourceAbsoluteExponent
    exact add_nonneg (add_nonneg hC₁
      (mul_nonneg hC₀ (Real.log_nonneg (le_max_left _ _))))
      (mul_nonneg (div_nonneg hC₀ (by norm_num)) (Real.log_nonneg (le_max_left _ _)))
  filter_upwards [
    giantSignedSourceMemoryTail_budget_eventually (ell+budget) C₀ Cv Cₐ A hC₀ hCv hCₐ hA,
    giantSignedSourceTiltedBoundary_budget_eventually q c C₀ k ell hM hq.le hq1.le hc hC₀,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))] with x htail htilt hL
  intro S B I _ _ _ _ PS PB _ _ hPS hPB hdis hVsmall hVmin hVmax hp hS hB
  dsimp only
  intro W hW patterns C hC hcost κ θ ζ K hK
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let ν := fun g => giantSignedTiltedPrimeLaw (PB g) (giantSignedSourceVisitQ q n)
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  obtain ⟨hν, hMass, hboundary⟩ := htilt S B PS PB hPS hdis
    (fun j => hvmin.trans_le (hVsmall j)) (fun g => hvmin.trans_le (hVmin g)) hp hB
  have hn := hnorm S B I PS PB k n budget ν hν hMass hPS hPB hdis hVsmall hVmin hVmax
    L C₁ W hL0 hW hS hB patterns C hC hcost κ θ ζ K hK hboundary
  exact (div_le_div_of_nonneg_right hn
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)).trans (htail (Fintype.card B) hB)

end
end ArtinMatthews
