module

public import ArtinMatthews.SpectralCuspWeightedGluingRepresentative
public import ArtinMatthews.SpectralCuspWeightedLocalIntegrability
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Compatible actual weighted cusp L² classes glue to one locally Lebesgue-integrable
representative on the full positive half-line. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

/-- Local L¹ follows from the actual L² measure density, localized to any containing open strip. -/
theorem spectralCuspGluedRepresentative_locallyIntegrableOn {w : ℝ} (hw : 0 < w)
    (a : ∀ n : ℕ, CuspVerticalL2 w (spectralCuspGluingHeight n))
    (hcompat : ∀ m n, m ≤ n → (a m : ℝ → ℂ)
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure (spectralCuspGluingHeight m)]
        (a n : ℝ → ℂ)) :
    LocallyIntegrableOn (spectralCuspGluedRepresentative w a) (Ioi 0) volume := by
  intro y hy
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < y from hy)
  have hn' : spectralCuspGluingHeight n < y := hn
  have hf := cuspVerticalL2_locallyIntegrableOn w (spectralCuspGluingHeight n)
    hw (spectralCuspGluingHeight_pos n) (a n)
  have hc := hf.congr (spectralCuspGluedRepresentative_ae_volume hw a hcompat n).symm
  obtain ⟨s, hs, hint⟩ := hc y hn'
  refine ⟨s, ?_, hint⟩
  apply mem_nhdsWithin_of_mem_nhds
  have hopen : Ioi (spectralCuspGluingHeight n) ∈ 𝓝 y :=
    isOpen_Ioi.mem_nhds (show y ∈ Ioi (spectralCuspGluingHeight n) from hn')
  simpa only [nhdsWithin_eq_nhds.mpr hopen] using hs

/-- Global representative theorem for the exact weighted L² spaces used by the cusp averages. -/
theorem spectralCuspWeightedGluing_exists {w : ℝ} (hw : 0 < w)
    (a : ∀ n : ℕ, CuspVerticalL2 w (spectralCuspGluingHeight n))
    (hcompat : ∀ m n, m ≤ n → (a m : ℝ → ℂ)
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure (spectralCuspGluingHeight m)]
        (a n : ℝ → ℂ)) :
    ∃ c : ℝ → ℂ, LocallyIntegrableOn c (Ioi 0) volume ∧
      ∀ n, c =ᵐ[(cuspHorizontalMeasure w univ) •
        cuspVerticalMeasure (spectralCuspGluingHeight n)] (a n : ℝ → ℂ) :=
  ⟨spectralCuspGluedRepresentative w a,
    spectralCuspGluedRepresentative_locallyIntegrableOn hw a hcompat,
    spectralCuspGluedRepresentative_ae hw a hcompat⟩

/-- A global representative with all the specified weighted restrictions is unique almost
 everywhere on positive heights. -/
theorem spectralCuspWeightedGluing_unique {w : ℝ} (hw : 0 < w) {c d : ℝ → ℂ}
    (hagree : ∀ n, c =ᵐ[(cuspHorizontalMeasure w univ) •
      cuspVerticalMeasure (spectralCuspGluingHeight n)] d) :
    c =ᵐ[volume.restrict (Ioi 0)] d := by
  have hall : ∀ᵐ y ∂volume, ∀ n, spectralCuspGluingHeight n < y → c y = d y := by
    apply ae_all_iff.mpr
    intro n
    exact ae_imp_of_ae_restrict
      ((spectralCuspVerticalL2_ae_iff hw (spectralCuspGluingHeight_pos n)).mp (hagree n))
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioi] with y hy hypos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < y from hypos)
  exact hy n hn

end
end ArtinMatthews
