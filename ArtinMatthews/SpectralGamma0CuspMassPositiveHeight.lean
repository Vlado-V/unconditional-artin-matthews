module

public import ArtinMatthews.SpectralGamma0CuspHeightRestriction
public import ArtinMatthews.SpectralCoreLocalizationChartCompact
public import ArtinMatthews.SpectralFiniteCoverIntegral
public import ArtinMatthews.SpectralGamma0CuspMassBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! All positive-height actual cusp restrictions are bounded by the complete
finite-chart mass norm, independently of the energy/derivative norm. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0_cusp_positive_height_mass_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ C > 0, ∀ ψ : h2SmoothCompactSeeds,
      (∫ z in hyperbolicCuspStrip (N : ℝ) Y,
        ‖gamma0CuspSection N ψ r z‖ ^ 2) ≤ C * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 := by
  classical
  let K : Set UpperHalfPlane :=
    {z | (z.re, z.im) ∈ spectralPlaneRectangle (N : ℝ) Y 1}
  let T : Set UpperHalfPlane := hyperbolicCuspStrip (N : ℝ) 1
  have hK : IsCompact K := spectralCoreChart_compact (N : ℝ) Y 1 hY
  obtain ⟨C0, hC0, hcompact⟩ := compact_chart_gamma0_cusp_mass_bound hK
  refine ⟨C0 + (N : ℝ) + 1, by positivity, fun ψ => ?_⟩
  let f : UpperHalfPlane → ℝ := fun z => ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖ ^ 2
  have hc : Continuous f := ((gamma0PoincareSeed N ψ.val).continuous.comp
    (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹))).norm.pow 2
  have ht : IntegrableOn f T ∧
      (∫ z in T, f z) ≤ ((N : ℝ) + 1) * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 :=
    gamma0_cusp_strip_mass_bound N ψ r
  have hT : MeasurableSet T :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hS : MeasurableSet (hyperbolicCuspStrip (N : ℝ) Y) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  let cover : Bool → Set UpperHalfPlane := fun b => if b then T else K
  have hcover : hyperbolicCuspStrip (N : ℝ) Y ⊆
      ⋃ b ∈ (Finset.univ : Finset Bool), cover b := by
    intro z hz
    by_cases hz1 : 1 < z.im
    · exact mem_iUnion₂.mpr ⟨true, Finset.mem_univ _, ⟨hz.1, hz1⟩⟩
    · apply mem_iUnion₂.mpr
      refine ⟨false, Finset.mem_univ _, ?_⟩
      change (z.re, z.im) ∈ spectralPlaneRectangle (N : ℝ) Y 1
      exact ⟨⟨by have := Nat.cast_nonneg (α := ℝ) N; linarith [hz.1.1], hz.1.2⟩,
        ⟨hz.2.le, le_of_not_gt hz1⟩⟩
  have hm : ∀ b ∈ (Finset.univ : Finset Bool), MeasurableSet (cover b) := by
    intro b _
    cases b
    · exact hK.measurableSet
    · exact hT
  have hi : ∀ b ∈ (Finset.univ : Finset Bool), IntegrableOn f (cover b) := by
    intro b _
    cases b
    · exact hc.continuousOn.integrableOn_compact hK
    · exact ht.1
  have hb := finite_cover_integrable_integral_le_sum volume Finset.univ cover hS hm
    hcover f (fun _ => sq_nonneg _) hc.aestronglyMeasurable hi
  have hbound : (∫ z in hyperbolicCuspStrip (N : ℝ) Y, f z) ≤
      (∫ z in K, f z) + ∫ z in T, f z := by
    simpa [cover, add_comm] using hb.2
  calc
    _ ≤ _ := hbound
    _ ≤ C0 * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 +
        ((N : ℝ) + 1) * ‖gamma0SmoothSeedMass N ψ‖ ^ 2 :=
      add_le_add (hcompact N ψ r) ht.2
    _ = _ := by ring

theorem gamma0CuspHeightSeedLp_mass_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ C > 0, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0CuspHeightSeedLp N r Y hY ψ‖ ≤ C * ‖gamma0SmoothSeedMass N ψ‖ := by
  obtain ⟨C, hC, hb⟩ := gamma0_cusp_positive_height_mass_bound N r Y hY
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun ψ => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hC.le]
  change ‖(gamma0CuspSection_memLp_positive_height N ψ r Y hY).toLp
    (gamma0CuspSection N ψ r)‖ ^ 2 ≤ C * ‖gamma0SmoothSeedMass N ψ‖ ^ 2
  rw [spectral_cusp_toLp_norm_square]
  exact hb ψ

end ArtinMatthews
