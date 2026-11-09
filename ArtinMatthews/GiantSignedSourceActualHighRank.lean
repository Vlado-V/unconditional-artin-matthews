module

public import ArtinMatthews.GiantSignedActualBirthEventBound
public import ArtinMatthews.GiantSignedSourceConditionalCost
public import ArtinMatthews.GiantSignedSourceInitialConditionalMass
public import ArtinMatthews.GiantSignedSourceHighRankBudget
public import Mathlib.Data.Fintype.Perm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual capped birth equality events above the source rank
threshold. The native tilted atoms pay every dependent birth. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

local instance actualHighRankPermutationFintype {B : Type*} [Fintype B] {M n H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M n H)
    (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance inferInstance inferInstance

private theorem actual_birth_cost_form {S B I : Type u} [Fintype S] [Fintype B]
    {n H k ell : ℕ} (patterns : Fin n → Finset I) (V : B → ℝ) (visitQ : Fin (n+1) → ℝ)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H)) (budget : ℕ)
    (ρ v vmin mass BS W Δ : ℝ) :
    let birth (o : GiantSignedBirthOperation n) := Δ^(giantSignedUniformBirthStageNonpivots σ o).card
    (birth .initial * mass^(Fintype.card B*(k+ell))) *
      ((∏ i, giantSignedActualBirthVisitCost V ρ visitQ v mass Δ σ i) *
        ∏ i, giantSignedActualBirthEdgeCost (S := S) (k := k) (ell := ell) ρ patterns v vmin mass
          budget BS W Δ σ i) =
    (birth .initial * mass^(Fintype.card B*(k+ell))) *
      (∏ i : Fin (n+1), birth (.visit i) *
        ∏ g, Real.exp (‖((-(1-visitQ i)*V g/ρ : ℝ) : ℂ)‖*mass*v)) *
      (∏ i : Fin n, birth (.edge i) * (((patterns i).card : ℝ)*W *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ mass (ell+budget))^Fintype.card B *
        BS^Fintype.card S)) := by
  intro birth
  have he : (∏ i, giantSignedActualBirthEdgeCost (S := S) (k := k) (ell := ell) ρ patterns v vmin mass
      budget BS W Δ σ i) = ∏ i : Fin n, birth (.edge i) * (((patterns i).card : ℝ)*W *
        (giantSignedEdgeUniformConstant ρ v vmin⁻¹ mass (ell+budget))^Fintype.card B *
        BS^Fintype.card S) := by
    apply Finset.prod_congr rfl
    intro i _
    unfold giantSignedActualBirthEdgeCost birth
    ring
  rw [he]
  simp only [giantSignedActualBirthVisitCost, Complex.norm_real, Real.norm_eq_abs, birth, mul_assoc]

theorem giantSignedSourceCappedBirth_high_rank_sum_eventually
    {q ρ C₀ vmin vmax v E c scale C₁ BS : ℝ} (k ell budget : ℕ)
    (hM : 1 ≤ k+ell) (hq : 0 < q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hC₀ : 0 ≤ C₀) (hvmin : 0 < vmin) (hvmax : 0 ≤ vmax) (hv : 1 ≤ v)
    (hc : 0 < c) (hC₁ : 0 ≤ C₁) (hBS : 0 ≤ BS)
    (hsmall : ∀ V : ℝ, vmin ≤ V → ∀ z : ℕ,
      V⁻¹ ^ ell * ((z : ℝ)+(ell : ℝ)) ^ ell * q ^ ((z : ℝ)/2) ≤ BS)
    (hrow : ∀ (n : ℕ) (i : Fin (n+1)), |giantSignedSourceVisitQ q n i / ρ^2| +
      |-(1-giantSignedSourceVisitQ q n i)/ρ|/v ≤ 1)
    (hscale : 2*(2*giantSignedSourceHighRankCostExponent C₀ C₁ BS ρ v vmin vmax (ell+budget)+E+1) ≤ scale) :
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
        (∀ g (p : PB g), Real.exp ((Real.log x)^c) ≤ (p.val : ℝ)) →
        (Fintype.card S : ℝ) ≤ C₀ * Real.log (Real.log x) →
        (Fintype.card B : ℝ) ≤ C₀ * Real.log (Real.log x) →
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      let H := giantSignedSourceMemoryLimit L
      let visitQ := giantSignedSourceVisitQ q n
      let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
      let V := fun g => bandReciprocalMass (PB g)
      ∀ (W : ℝ), 0 ≤ W → ∀ (θ : ℝ)
        (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k)),
        (∀ i p, p ∈ patterns i → ∀ g, (C i p g).card ≤ budget) →
        (∀ i, ((patterns i).card : ℝ)*W ≤ L^C₁) →
      ∀ (κ : Fin n → ℤ) (ζ : Fin n → ℝ)
        (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell),
        (∀ i p, p ∈ patterns i → ∀ a b aux, ‖K i p a b aux‖ ≤ W) →
      (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H),
        if giantSignedSourceRankCutoff c scale x ≤ giantSignedUniformBirthRank σ then
          ‖giantSignedCappedBirthEventBoundary (PS := PS) H ν V q ρ θ
            n patterns C κ visitQ ζ K (fun _ _ _ _ => 1) σ‖ else 0) ≤ (L^(-E))^n := by
  let Ch := giantSignedSourceHighRankCostExponent C₀ C₁ BS ρ v vmin vmax (ell+budget)
  let K₀ := 2/vmin
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hCh := giantSignedSourceHighRankCostExponent_nonneg (BS := BS) (vmin := vmin)
    (ell+budget) hC₀ hC₁ hvmax hρ hv0
  have hK₀ : 0 ≤ K₀ := by unfold K₀; positivity
  filter_upwards [
    giantSignedSourceBirth_high_rank_sum_eventually C₀ Ch E c scale K₀ (k+ell) hC₀ hCh hc hK₀ hscale,
    giantSignedSourceInitialConditionalMass_eventually k ell hM hq.le hq1 hc hC₀ hvmin,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))] with x hhigh hmass hL
  intro S B I _ _ _ _ PS PB _ _ hPS hPB hdis hVsmall hVmin hVmax hp hS hB
  dsimp only
  intro W hW θ patterns C hCap hcost κ ζ K hK
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let H := giantSignedSourceMemoryLimit L
  let visitQ := giantSignedSourceVisitQ q n
  let ν := fun g => giantSignedTiltedPrimeLaw (PB g) visitQ
  let V := fun g => bandReciprocalMass (PB g)
  let mass := giantSignedSourceConditionalMass c x
  let Δ := K₀/Real.exp (L^c)
  have hΔ : 0 ≤ Δ := div_nonneg hK₀ (Real.exp_nonneg _)
  have hVS (j : S) : 0 < bandReciprocalMass (PS j) := hvmin.trans_le (hVsmall j)
  have hVB (g : B) : 0 < V g := hvmin.trans_le (hVmin g)
  have hQ0 (i : Fin (n+1)) : 0 ≤ visitQ i := (giantSignedSourceVisitQ_bounds hq.le hq1 n i).1
  have hQ1 (i : Fin (n+1)) : visitQ i ≤ 1 := by
    have hs : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
    exact (giantSignedSourceVisitQ_bounds hq.le hq1 n i).2.trans hs
  obtain ⟨hmass1,hmass2,hinit,hν,hMass,hatom⟩ := hmass B PB hVmin hp hB
  let F := giantSignedCappedBirthEventBoundary (PS := PS) H ν V q ρ θ
    n patterns C κ visitQ ζ K (fun _ _ _ _ => 1)
  refine hhigh B hB F ?_
  intro σ _
  have hbound := giantSignedCappedBirthEventBoundary_norm_le (H := H) hPS hPB hdis hVS hVB ν hν V
    hvmin hVmin hmass1 hq hq1 hBS (fun j z => hsmall _ (hVsmall j) z)
    hρ.le hρ1 hv hW hΔ hatom hMass budget θ patterns C hCap κ visitQ ζ (hrow n) K hK
    (fun _ _ _ _ => 1) (fun _ _ _ _ _ => norm_one.le) σ
  have hcost' := giantSignedSourceConditionalCosts_le (S := S) patterns V visitQ σ (ell+budget)
    (vmin := vmin) hL hC₀ hC₁ hBS hρ hρ1 hv0 hvmax hW hΔ (zero_le_one.trans hmass1)
    hmass2 hinit (fun g => (hVB g).le) hVmax hQ0 hQ1 hS hB hcost
  have hform := actual_birth_cost_form (S := S) (k := k) (ell := ell)
    patterns V visitQ σ budget ρ v vmin mass BS W Δ
  exact hbound.trans (hform.le.trans hcost')

end
end ArtinMatthews
