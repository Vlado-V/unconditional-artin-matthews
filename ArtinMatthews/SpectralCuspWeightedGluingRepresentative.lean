module

public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers


set_option backward.privateInPublic true
@[expose] public section

/-! Countable compatible weighted cusp classes admit one actual representative on positive heights.
The construction uses only a countable null-set union; no continuous representatives are chosen. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

/-- The nested height exhaustion used for the actual cusp constant terms. -/
def spectralCuspGluingHeight (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem spectralCuspGluingHeight_pos (n : ℕ) : 0 < spectralCuspGluingHeight n := by
  unfold spectralCuspGluingHeight
  positivity

/-- Weighted strip null sets are exactly Lebesgue null sets above the strip height. -/
theorem spectralCuspVerticalL2_ae_iff {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    {P : ℝ → Prop} :
    (∀ᵐ y ∂(cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y, P y) ↔
      ∀ᵐ y ∂volume.restrict (Ioi Y), P y := by
  rw [cuspHorizontalMeasure_univ,
    Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hw))]
  exact spectralHorizontal_cuspVertical_ae_iff hY

/-- At each positive height use the first class whose strip contains that height. -/
def spectralCuspGluedRepresentative (w : ℝ)
    (a : ∀ n : ℕ, CuspVerticalL2 w (spectralCuspGluingHeight n)) (y : ℝ) : ℂ :=
  if hy : 0 < y then a (Nat.find (exists_nat_one_div_lt hy)) y else 0

/-- Ordered compatibility implies simultaneous pairwise agreement on overlaps outside one null set. -/
theorem spectralCuspGluing_pairwise_ae {w : ℝ} (hw : 0 < w)
    (a : ∀ n : ℕ, CuspVerticalL2 w (spectralCuspGluingHeight n))
    (hcompat : ∀ m n, m ≤ n → (a m : ℝ → ℂ)
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure (spectralCuspGluingHeight m)]
        (a n : ℝ → ℂ)) :
    ∀ᵐ y ∂volume, ∀ m n, spectralCuspGluingHeight m < y →
      spectralCuspGluingHeight n < y → a m y = a n y := by
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro n
  rcases le_total m n with hmn | hnm
  · have h := (spectralCuspVerticalL2_ae_iff hw (spectralCuspGluingHeight_pos m)).mp
      (hcompat m n hmn)
    filter_upwards [ae_imp_of_ae_restrict h] with y hy
    exact fun hym _ => hy hym
  · have h := (spectralCuspVerticalL2_ae_iff hw (spectralCuspGluingHeight_pos n)).mp
      (hcompat n m hnm)
    filter_upwards [ae_imp_of_ae_restrict h] with y hy
    exact fun _ hyn => (hy hyn).symm

/-- The chosen representative agrees with each original class in its actual weighted measure. -/
theorem spectralCuspGluedRepresentative_ae {w : ℝ} (hw : 0 < w)
    (a : ∀ n : ℕ, CuspVerticalL2 w (spectralCuspGluingHeight n))
    (hcompat : ∀ m n, m ≤ n → (a m : ℝ → ℂ)
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure (spectralCuspGluingHeight m)]
        (a n : ℝ → ℂ)) (n : ℕ) :
    spectralCuspGluedRepresentative w a
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure (spectralCuspGluingHeight n)]
        (a n : ℝ → ℂ) := by
  apply (spectralCuspVerticalL2_ae_iff hw (spectralCuspGluingHeight_pos n)).mpr
  filter_upwards [ae_restrict_of_ae (spectralCuspGluing_pairwise_ae hw a hcompat),
    ae_restrict_mem measurableSet_Ioi] with y hy hyn
  have hypos : 0 < y := (spectralCuspGluingHeight_pos n).trans hyn
  unfold spectralCuspGluedRepresentative
  rw [dite_eq_left hypos]
  exact hy _ n (Nat.find_spec (exists_nat_one_div_lt hypos)) hyn

/-- Agreement also holds in ordinary Lebesgue measure on each open strip. -/
theorem spectralCuspGluedRepresentative_ae_volume {w : ℝ} (hw : 0 < w)
    (a : ∀ n : ℕ, CuspVerticalL2 w (spectralCuspGluingHeight n))
    (hcompat : ∀ m n, m ≤ n → (a m : ℝ → ℂ)
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure (spectralCuspGluingHeight m)]
        (a n : ℝ → ℂ)) (n : ℕ) :
    spectralCuspGluedRepresentative w a =ᵐ[volume.restrict (Ioi (spectralCuspGluingHeight n))]
      (a n : ℝ → ℂ) :=
  (spectralCuspVerticalL2_ae_iff hw (spectralCuspGluingHeight_pos n)).mp
    (spectralCuspGluedRepresentative_ae hw a hcompat n)

end
end ArtinMatthews
