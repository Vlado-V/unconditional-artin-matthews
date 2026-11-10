module

public import ArtinMatthews.SpectralGamma0CuspPositiveHeightCompact
public import ArtinMatthews.SpectralCoreLocalizationChartCompact
public import ArtinMatthews.SpectralFiniteCoverIntegral
public import ArtinMatthews.SpectralGamma0CuspEnergy
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

/-! Genuine cusp-strip mass and energy bounds at every positive height.
These are not restricted to the height-one tail region. -/

namespace ArtinMatthews
noncomputable section

open Set MeasureTheory Filter
open scoped MatrixGroups

theorem gamma0_cusp_positive_height_energy_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ C > 0, ∀ ψ : h2SmoothCompactSeeds,
      IntegrableOn (gamma0CuspEnergyDensity N ψ r) (hyperbolicCuspStrip (N : ℝ) Y) ∧
      (∫ z in hyperbolicCuspStrip (N : ℝ) Y, gamma0CuspEnergyDensity N ψ r z) ≤
        C*‖gamma0EnergyTest N ψ‖^2 := by
  classical
  let K : Set UpperHalfPlane :=
    {z | (z.re,z.im) ∈ spectralPlaneRectangle (N : ℝ) Y 1}
  let T : Set UpperHalfPlane := hyperbolicCuspStrip (N : ℝ) 1
  have hK : IsCompact K := spectralCoreChart_compact (N : ℝ) Y 1 hY
  obtain ⟨C0,hC0,hcompact⟩ := compact_chart_gamma0_cusp_energy_bound r hK
  refine ⟨C0+(N : ℝ)+1, by positivity, fun ψ => ?_⟩
  have ht : IntegrableOn (gamma0CuspEnergyDensity N ψ r) T ∧
      (∫ z in T, gamma0CuspEnergyDensity N ψ r z) ≤
        ((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖^2 := by
    have he : gamma0CuspEnergyDensity N ψ r = fun z : UpperHalfPlane =>
        ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖^2+
          h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z) := by
      funext z
      rw [gamma0CuspEnergyDensity,gamma0CuspSection_energy]
      rfl
    rw [he]
    exact gamma0_cusp_strip_energy_bound N ψ r
  have hT : MeasurableSet T :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hS : MeasurableSet (hyperbolicCuspStrip (N : ℝ) Y) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  let cover : Bool → Set UpperHalfPlane := fun b => if b then T else K
  have hcover : hyperbolicCuspStrip (N : ℝ) Y ⊆ ⋃ b ∈ (Finset.univ : Finset Bool), cover b := by
    intro z hz
    by_cases hz1 : 1 < z.im
    · exact mem_iUnion₂.mpr ⟨true,Finset.mem_univ _,⟨hz.1,hz1⟩⟩
    · apply mem_iUnion₂.mpr
      refine ⟨false,Finset.mem_univ _,?_⟩
      change (z.re,z.im) ∈ spectralPlaneRectangle (N : ℝ) Y 1
      exact ⟨⟨by have := Nat.cast_nonneg (α := ℝ) N; linarith [hz.1.1],hz.1.2⟩,
        ⟨hz.2.le,le_of_not_gt hz1⟩⟩
  have hm : ∀ b ∈ (Finset.univ : Finset Bool), MeasurableSet (cover b) := by
    intro b _
    cases b
    · exact hK.measurableSet
    · exact hT
  have hi : ∀ b ∈ (Finset.univ : Finset Bool),
      IntegrableOn (gamma0CuspEnergyDensity N ψ r) (cover b) := by
    intro b _
    cases b
    · exact gamma0CuspEnergyDensity_integrableOn_compact N ψ r hK
    · exact ht.1
  have hc := finite_cover_integrable_integral_le_sum volume Finset.univ cover hS hm hcover
    (gamma0CuspEnergyDensity N ψ r) (gamma0CuspEnergyDensity_nonneg N ψ r)
    (gamma0CuspEnergyDensity_continuous N ψ r).aestronglyMeasurable hi
  refine ⟨hc.1,?_⟩
  have hbound : (∫ z in hyperbolicCuspStrip (N : ℝ) Y, gamma0CuspEnergyDensity N ψ r z) ≤
      (∫ z in K, gamma0CuspEnergyDensity N ψ r z)+(∫ z in T, gamma0CuspEnergyDensity N ψ r z) := by
    simpa [cover,add_comm] using hc.2
  calc
    _ ≤ _ := hbound
    _ ≤ C0*‖gamma0EnergyTest N ψ‖^2+((N : ℝ)+1)*‖gamma0EnergyTest N ψ‖^2 :=
      add_le_add (hcompact N ψ) ht.2
    _ = _ := by ring

theorem gamma0CuspSection_memLp_positive_height (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    MemLp (gamma0CuspSection N ψ r) 2 (volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)) := by
  obtain ⟨_,_,hbound⟩ := gamma0_cusp_positive_height_energy_bound N r Y hY
  have ht := (hbound ψ).1
  have hv : Continuous (gamma0CuspSection N ψ r) := by
    change Continuous ((gamma0PoincareSeed N ψ.val) ∘
      fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z)
    exact (gamma0PoincareSeed N ψ.val).continuous.comp (continuous_const_smul _)
  apply (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
  apply ht.mono' (hv.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  change ‖‖gamma0CuspSection N ψ r z‖^2‖ ≤ gamma0CuspEnergyDensity N ψ r z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact le_add_of_nonneg_right (h2SectionEnergy_nonneg _ _)

end
end ArtinMatthews
