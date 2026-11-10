module

public import ArtinMatthews.SpectralHeightPartialProfile
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The native height cutoffs become exactly one on each fixed compact
positive-height set. In particular the zero geometric sector stabilizes. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ArtinMatthews

theorem spectralHeightAnnularPartial_eventually_one_on_compact (S : Set ℝ)
    (hS : IsCompact S) (hpos : S ⊆ Ioi (0 : ℝ)) :
    ∀ᶠ K : ℕ in atTop, ∀ y ∈ S, spectralHeightAnnularPartial K y = 1 := by
  by_cases hne : S.Nonempty
  · obtain ⟨b,hb⟩ := hS.exists_isLeast hne
    obtain ⟨d,hd⟩ := hS.exists_isGreatest hne
    have hb₀ : 0 < b := hpos hb.1
    have ht : Tendsto (fun K : ℕ => (2 : ℝ)^(K+1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    filter_upwards [ht.eventually_ge_atTop (2/b),ht.eventually_ge_atTop d] with K hK₁ hK₂ y hy
    have hc : 0 < (2 : ℝ)^(K+1) := by positivity
    have hlow : 2 ≤ (2 : ℝ)^(K+1)*y :=
      ((div_le_iff₀ hb₀).mp hK₁).trans (mul_le_mul_of_nonneg_left (hb.2 hy) hc.le)
    have hhigh : y/(2 : ℝ)^(K+1) ≤ 1 := (div_le_one hc).mpr ((hd.2 hy).trans hK₂)
    rw [spectralHeightAnnularPartial_eq,spectralHeightCutStep_one hlow,
      spectralHeightCutStep_zero hhigh,sub_zero]
  · exact Eventually.of_forall (fun _ y hy => (hne ⟨y,hy⟩).elim)

theorem spectralHeightProfilePartial_eventually_height_pairing (ρ η : ℝ → ℝ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    ∀ᶠ K : ℕ in atTop,
      cuspFourierHeightPairing ρ (spectralHeightProfilePartial K η) = cuspFourierHeightPairing ρ η := by
  filter_upwards [spectralHeightAnnularPartial_eventually_one_on_compact (tsupport ρ) hcρ hpρ]
    with K hK
  unfold cuspFourierHeightPairing
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  change ρ y*spectralHeightProfilePartial K η y/y^2 = ρ y*η y/y^2
  by_cases hy : ρ y = 0
  · simp only [hy,zero_mul,zero_div]
  · rw [spectralHeightProfilePartial_apply,hK y (subset_tsupport ρ hy),one_mul]

end ArtinMatthews
