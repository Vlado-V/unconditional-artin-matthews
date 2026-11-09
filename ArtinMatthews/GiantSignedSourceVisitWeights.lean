module

public import ArtinMatthews.GiantSignedGhostWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The original endpoint visits use sqrt q and interior visits use q.
One memory weight is chosen before the word length and all group carriers. -/
namespace ArtinMatthews
noncomputable section

def giantSignedSourceVisitQ (q : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val = 0 ∨ i.val = n then Real.sqrt q else q

theorem giantSignedSourceVisitQ_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ giantSignedSourceVisitQ q n i ∧ giantSignedSourceVisitQ q n i ≤ Real.sqrt q := by
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq0
  have hs1 : Real.sqrt q ≤ 1 := by nlinarith
  have hqs : q ≤ Real.sqrt q := by nlinarith
  unfold giantSignedSourceVisitQ
  split_ifs
  · exact ⟨hs0, le_rfl⟩
  · exact ⟨hq0, hqs⟩

theorem giantSignedSourceGhostWeight_exists {q ρ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ ^ 2)
    (Vmax : ℝ) :
    ∃ v : ℝ, 1 < v ∧ ∀ qi Vg : ℝ, 0 ≤ qi → qi ≤ Real.sqrt q →
      0 ≤ Vg → Vg ≤ Vmax →
      |qi / ρ ^ 2| + |-(1-qi) / ρ| / v < 1 ∧
      |qi / ρ ^ 2| + 2 * |-(1-qi) * Vg / ρ| / v < 1 := by
  obtain ⟨v, hv, h⟩ := giantSignedGhostWeight_exists
    (Real.sqrt q / ρ ^ 2) (Vmax / ρ) (1 / ρ)
    (giantSignedGhost_source_A_lt_one hρ hgap)
  refine ⟨v, hv, ?_⟩
  intro qi Vg hqi0 hqis hVg0 hVgmax
  have hs2 := Real.sq_sqrt hq0
  have hs0 := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := by nlinarith
  have hqi1 : qi ≤ 1 := hqis.trans hs1
  have hA0 : 0 ≤ qi / ρ ^ 2 := div_nonneg hqi0 (sq_nonneg ρ)
  have hA : qi / ρ ^ 2 ≤ Real.sqrt q / ρ ^ 2 :=
    div_le_div_of_nonneg_right hqis (sq_nonneg ρ)
  have hC : |-(1-qi) * Vg / ρ| ≤ Vmax / ρ := by
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hqi1),
      abs_of_nonneg hVg0, abs_of_pos hρ]
    apply div_le_div_of_nonneg_right _ hρ.le
    exact (mul_le_of_le_one_left hVg0 (by linarith : 1 - qi ≤ 1)).trans hVgmax
  have hD : |-(1-qi) / ρ| ≤ 1 / ρ := by
    rw [abs_div, abs_neg, abs_of_nonneg (sub_nonneg.mpr hqi1), abs_of_pos hρ]
    exact div_le_div_of_nonneg_right (by linarith) hρ.le
  simpa only [abs_of_nonneg hA0] using
    h (qi / ρ ^ 2) (-(1-qi) * Vg / ρ) (-(1-qi) / ρ) hA hC hD

theorem giantSignedSourceVisitWeights_exists {q ρ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ ^ 2)
    (Vmax : ℝ) :
    ∃ v : ℝ, 1 < v ∧ ∀ (n : ℕ) (i : Fin (n + 1)) (Vg : ℝ),
      0 ≤ Vg → Vg ≤ Vmax →
      |giantSignedSourceVisitQ q n i / ρ ^ 2| +
        |-(1-giantSignedSourceVisitQ q n i) / ρ| / v < 1 ∧
      |giantSignedSourceVisitQ q n i / ρ ^ 2| +
        2 * |-(1-giantSignedSourceVisitQ q n i) * Vg / ρ| / v < 1 := by
  obtain ⟨v, hv, h⟩ := giantSignedSourceGhostWeight_exists hq0 hq1 hρ hgap Vmax
  refine ⟨v, hv, ?_⟩
  intro n i Vg hVg0 hVgmax
  exact h _ Vg (giantSignedSourceVisitQ_bounds hq0 hq1 n i).1
    (giantSignedSourceVisitQ_bounds hq0 hq1 n i).2 hVg0 hVgmax

end
end ArtinMatthews
