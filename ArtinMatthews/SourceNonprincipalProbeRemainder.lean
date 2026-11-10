module

public import ArtinMatthews.SourceNonprincipalRowSeries
public import ArtinMatthews.SourceNonprincipalDyadAggregation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nonprincipal complement of the physical source contour
has the manuscript's fixed power saving. The original row sum is
absolutely convergent before it is reindexed or shifted. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Filter Asymptotics
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical BigOperators Topology
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀

theorem sourcePoissonNonprincipalRowSeries_source06_bound
    (hS : standardWeilBadPlaces F ⊆ S) (hcut : principalAngularCutoff F J ⊆ S)
    (v : InfinitePlace F) :
    (fun Z : ℝ => sourcePoissonNonprincipalRowSeries F S₀ hζ η hJ v
      (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z) =O[atTop]
      (fun Z : ℝ => Z^(7/15-1/2500 : ℝ)) := by
  obtain ⟨C, U₀, hC, _, h⟩ := exists_sourcePoissonNonprincipalDyad_sum_bound F S₀ hζ η hJ hcut v
  have hcut₀ : probePrimeCutoff F ⊆ S := probePrimeCutoff_subset_principalAngularCutoff.trans hcut
  let W := ∑' j : ℕ, sourceNonprincipalDyadicWeight j
  refine IsBigO.of_bound (C*W) ?_
  have hpow : Tendsto (fun Z : ℝ => Z^(9/100 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpow.eventually (eventually_ge_atTop U₀)] with Z hZ hth
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ
  let X := Z^(9/10 : ℝ)
  let Y := Z^(133/1000 : ℝ)
  let f (j : ℕ) := sourcePoissonNonprincipalDyadSum F S₀ hζ η hJ v X Y Z j
  let B := C*Z^sourceNonprincipalTargetExponent
  have hB := sourceNonprincipalDyadicWeight_summable.mul_left B
  have hb (j : ℕ) : ‖f j‖ ≤ B*sourceNonprincipalDyadicWeight j := by
    exact (h j Z hZ hth).trans_eq (by dsimp only [B]; ring)
  have hf := hB.of_nonneg_of_le (fun j => norm_nonneg (f j)) hb
  change ‖sourcePoissonNonprincipalRowSeries F S₀ hζ η hJ v X Y Z‖ ≤
    C*W*‖Z^sourceNonprincipalTargetExponent‖
  rw [sourcePoissonNonprincipalRowSeries_eq_dyads F S₀ hζ η hJ hS hcut₀ v
    (Real.rpow_pos_of_pos hZ₀ _) (Real.rpow_pos_of_pos hZ₀ _) hZ₀,
    Real.norm_of_nonneg (Real.rpow_nonneg hZ₀.le _)]
  calc
    _ ≤ ∑' j, ‖f j‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' j, B*sourceNonprincipalDyadicWeight j := hf.tsum_le_tsum hb hB
    _ = _ := by rw [tsum_mul_left]; dsimp only [W,B]; ring

end
end ArtinMatthews.SourceEulerAssembly
