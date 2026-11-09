module

public import ArtinMatthews.PositiveDensityCandidateCRT
public import ArtinMatthews.PositiveDensitySmallIndexBound
public import ArtinMatthews.VaryingKummerAnalyticKummerSplitEstimate


set_option backward.privateInPublic true
@[expose] public section

/-! The small-index input to the final weighted sieve for the literal
enlarged progression. The zero-region estimate remains explicit. -/

noncomputable section
namespace ArtinMatthews

open Filter VaryingKummerAnalytic
open scoped Topology

theorem giantSieve_enlarged_smallIndex_bound_of_zero_region
    {S : Finset ℤ} (hS : AdmissibleBases S) {δ ε : ℝ} (hδ : δ ≤ 1) (hεδ : ε < δ)
    (hzero : ∀ a ∈ S, ∀ q : ℕ, q.Prime → 2 < q → a.natAbs ≤ q →
      ∀ ρ : ℂ, mixedCompletedDedekindXi (primeKummerField q a) ρ = 0 → ρ.re ≤ 1 - δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℕ), 3 ≤ Y → (∀ a ∈ S, a.natAbs ≤ Y) →
      ∀ (u r₃ : ℕ) (hprog : IsQuadraticProgressionFor S u r₃)
        (select : ℕ → Prop),
        (∀ p, select p → r₃ = 2 ∨ ∀ a ∈ S, ¬ IsCubeMod p a) →
        ∀ (Φ : ℝ → ℝ), (∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) →
        ∀ (T : ℝ), 1 < T → T < 2 → Function.support Φ ⊆ Set.Ioo 1 T →
        let U := giantSieveEnlargedUnits hprog Y
        let error := fun x : ℝ => 4 * C * (S.card : ℝ) * x ^ (1 - δ + ε)
        error =o[atTop] (fun x : ℝ => x / Real.log x) ∧
          ∀ᶠ x : ℝ in atTop,
            ((smallIndexCandidates S (giantSieveCandidates U select ε Φ T x)
              (exceptionalExponentCutoff ε x)).card : ℝ) ≤
              (C * (S.card : ℝ) / Y) * (x / Real.log x) + error x := by
  obtain ⟨C, hC, hbound⟩ := exists_primeKummer_split_count_bound_of_zero_region
  refine ⟨C, hC, ?_⟩
  intro Y hY habs u r₃ hprog select hselect Φ hΦ T hT₁ hT₂ hs
  let U := giantSieveEnlargedUnits hprog Y
  refine ⟨giantSieve_index_error_isLittleO _ hεδ, ?_⟩
  filter_upwards [giantSieveCandidates_structural_eventually hS U select ε Φ hΦ hT₁ hT₂ hs,
    eventually_ge_atTop (4 : ℝ)] with x hstruct hx
  refine giantSieve_smallIndex_card_le_of_split hx (by linarith) hC.le hY habs
    (fun p hp => ⟨(hstruct p hp).1, (hstruct p hp).2.1, (hstruct p hp).2.2.1⟩)
    (fun p hp => giantSieveCandidate_enlarged_no_small_index hprog hselect hp (hstruct p hp).2.2.1)
    ?_
  intro a ha q hq hq₂ haq R hR
  obtain ⟨ha₀, ha₁, ham₁⟩ := hS.2 a ha
  exact hbound a ha₀ ha₁ ham₁ q hq haq x (1 - δ) R (by linarith)
    (sub_nonneg.mpr hδ) (hzero a ha q hq hq₂ haq) hR

end ArtinMatthews
