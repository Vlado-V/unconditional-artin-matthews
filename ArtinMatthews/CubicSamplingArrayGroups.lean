module

public import ArtinMatthews.GiantActualRoughSieve
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Grouping equal literal band labels retains their original multiplicity,
including products of arrays with shared bands. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def cubicSamplingBandLabels {J : Type*} [Fintype J] (e : J → ℝ) : Finset ℝ :=
  Finset.univ.image e

def cubicSamplingBandMultiplicity {J : Type*} [Fintype J] (e : J → ℝ) (s : ℝ) : ℕ :=
  (Finset.univ.filter (fun j => e j = s)).card

theorem cubicSampling_bandMultiplicity_pos {J : Type*} [Fintype J] (e : J → ℝ)
    (s : ↥(cubicSamplingBandLabels e)) : 0 < cubicSamplingBandMultiplicity e s := by
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp s.2
  exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, he⟩⟩

theorem cubicSampling_literalArray_eq_grouped {J : Type*} [Fintype J] (e : J → ℝ)
    (x : ℝ) (u : ℕ) :
    literalMarkedArrayWeight e x u =
      ∏ s : ↥(cubicSamplingBandLabels e),
        (bandWeight (markedLogPowerBand s x) (bandReciprocalMass (markedLogPowerBand s x)) u) ^
          cubicSamplingBandMultiplicity e s := by
  let F (s : ℝ) := bandWeight (markedLogPowerBand s x)
    (bandReciprocalMass (markedLogPowerBand s x)) u
  change (∏ j, F (e j)) =
    ∏ s : ↥(cubicSamplingBandLabels e), F s ^ cubicSamplingBandMultiplicity e s
  rw [Finset.prod_coe_sort (cubicSamplingBandLabels e)
    (fun s => F s ^ cubicSamplingBandMultiplicity e s)]
  have hmap (j : J) (hj : j ∈ Finset.univ) : e j ∈ cubicSamplingBandLabels e :=
    Finset.mem_image.mpr ⟨j, hj, rfl⟩
  simpa only [Finset.prod_const, cubicSamplingBandMultiplicity] using
    (Finset.prod_fiberwise_of_maps_to' hmap F).symm

end ArtinMatthews
