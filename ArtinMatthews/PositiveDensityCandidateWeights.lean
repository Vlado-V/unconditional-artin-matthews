module

public import ArtinMatthews.PositiveDensityCandidates
public import ArtinMatthews.GiantProgressionUncentered
public import ArtinMatthews.CubicFrobeniusConditionKummer


set_option backward.privateInPublic true
@[expose] public section

/-! Exact comparison of the Section 10.3 candidate weights with the
uncentered prime-predecessor statistic. The ordinary and cubic selections
use the original residue indicator and giant-divisor count. -/

namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def giantSelectedPrimeTest {M : ℕ} (U : Finset (ZMod M)ˣ)
    (select : ℕ → Prop) (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ p ∈ giantPrimeMeanRange T x, if select p then
    (giantSieveWeight Φ x p:ℂ) * giantUnitResidueIndicator U p *
      (((giantPrimeFactors (p-1) x ε).card:ℝ):ℂ)
    else 0

theorem giantSelectedPrimeTest_all {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε : ℝ) (Φ : ℝ → ℝ) (T x : ℝ) :
    giantSelectedPrimeTest U (fun _ => True) ε Φ T x = giantUncenteredPrimeTest U ε Φ T x := by
  simp only [giantSelectedPrimeTest, giantUncenteredPrimeTest, giantSieveWeight, ite_true]

def giantCubicSieveSelection (S : Finset ℤ) (E : Finset ℕ) (p : ℕ) : Prop :=
  p ∉ E ∧ ∀ a ∈ S, ¬ IsCubeMod p a

theorem giantCubicSieveSelection_iff_frobenius {S : Finset ℤ} (E : Finset ℕ)
    {p : ℕ} [Fact p.Prime] (D : IntegralFrobeniusData (integerCubicField S) p)
    (hp₃ : p % 3 = 1) (ha₀ : ∀ a ∈ S, (a : ZMod p) ≠ 0) :
    giantCubicSieveSelection S E p ↔ p ∉ E ∧
      relativeCubicFrobenius D hp₃ ∈ cubicNonfixingSet S := by
  rw [giantCubicSieveSelection, relativeCubicFrobenius_mem_iff D hp₃ ha₀]

theorem giantSieveCandidates_weighted_count {M : ℕ} (U : Finset (ZMod M)ˣ)
    (select : ℕ → Prop) (Φ : ℝ → ℝ) {ε T x : ℝ}
    (hT : 0 ≤ T) (hT₂ : T ≤ 2) (hx : 4 ≤ x) (hε : ε ≤ 1/4) :
    ((∑ p ∈ giantSieveCandidates U select ε Φ T x, giantSieveWeight Φ x p : ℝ):ℂ) =
      giantSelectedPrimeTest U select ε Φ T x := by
  classical
  rw [Complex.ofReal_sum]
  unfold giantSieveCandidates giantSelectedPrimeTest
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hs : select p
  · by_cases hu : ∃ u ∈ U, (u : ZMod M) = (p : ZMod M)
    · by_cases hg : (giantPrimeFactors (p-1) x ε).Nonempty
      · have hpP : p.Prime := (Finset.mem_filter.mp hp).2
        have hx₀ : 0 ≤ x := by linarith
        have hn : 0 < p-1 := by have := hpP.two_le; omega
        have hn₂ : ((p-1 : ℕ):ℝ) ≤ 2*x :=
          (giantPrimeMeanRange_predecessor_le hT hx₀ hp).trans
            (mul_le_mul_of_nonneg_right hT₂ hx₀)
        have hcard : (giantPrimeFactors (p-1) x ε).card = 1 := le_antisymm
          (giantPrimeFactors_card_le_one hn hn₂ hx hε) (Finset.card_pos.mpr hg)
        have hI : giantUnitResidueIndicator U p = 1 := by
          unfold giantUnitResidueIndicator
          exact ite_eq_left (Finset.mem_image.mpr hu)
        by_cases hw : giantSieveWeight Φ x p = 0
        · simp [hw]
        · simp [hs,hu,hg,hcard,hI,hw]
      · simp [Finset.not_nonempty_iff_eq_empty.mp hg]
    · have hI : giantUnitResidueIndicator U p = 0 := by
        unfold giantUnitResidueIndicator
        exact ite_eq_right (fun h => hu (Finset.mem_image.mp h))
      simp [hu,hI]
  · simp [hs]

/-- The exact normalized statistic limit supplies the weighted candidate
lower bound with half of its positive leading coefficient. -/
theorem giantSieveCandidates_weighted_lower_of_mean {M : ℕ} (U : Finset (ZMod M)ˣ)
    (select : ℕ → Prop) (Φ : ℝ → ℝ) {ε T κ : ℝ}
    (hT : 0 ≤ T) (hT₂ : T ≤ 2) (hε : ε ≤ 1/4) (hκ : 0 < κ)
    (hmean : Tendsto (fun x : ℝ => ((Real.log x/x : ℝ):ℂ) *
      giantSelectedPrimeTest U select ε Φ T x) atTop (𝓝 (κ:ℂ))) :
    ∀ᶠ x : ℝ in atTop, (κ/2)*(x/Real.log x) ≤
      ∑ p ∈ giantSieveCandidates U select ε Φ T x, giantSieveWeight Φ x p := by
  have hRe : Tendsto (fun x : ℝ => (((Real.log x/x : ℝ):ℂ) *
      giantSelectedPrimeTest U select ε Φ T x).re) atTop (𝓝 κ) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hmean
  have hhalf : κ/2 < κ := by linarith
  filter_upwards [hRe.eventually (lt_mem_nhds hhalf), eventually_ge_atTop (4:ℝ)] with x hlow hx
  change κ/2 < (((Real.log x/x : ℝ):ℂ) * giantSelectedPrimeTest U select ε Φ T x).re at hlow
  rw [← giantSieveCandidates_weighted_count U select Φ hT hT₂ hx hε,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hlow
  have hx₀ : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ = (κ/2)/(Real.log x/x) := by field_simp
    _ ≤ _ := (div_le_iff₀ (div_pos hlog hx₀)).mpr (by simpa only [mul_comm] using hlow.le)

end
end ArtinMatthews
