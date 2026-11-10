module

public import ArtinMatthews.SourceArchHyperbolicDensity
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! The actual Euclidean upper chart and its measure-preserving inverse. -/
namespace ArtinMatthews.SourceArchJacquet
open MeasureTheory OAI.CubicEisenstein Set
noncomputable section

lemma sourceArchSpatialCoordinates_symm_apply (p : ℂ × ℝ) :
    sourceArchSpatialCoordinates.symm p = WithLp.toLp 2 ![p.1.re, p.1.im, p.2] := by
  apply sourceArchSpatialCoordinates.injective
  rw [MeasurableEquiv.apply_symm_apply, sourceArchSpatialCoordinates_apply]
  rfl

def sourceArchSpatialHomeomorph : EuclideanSpatial ≃ₜ (ℂ × ℝ) where
  toEquiv := sourceArchSpatialCoordinates.toEquiv
  continuous_toFun := by
    change Continuous (fun p : EuclideanSpatial => ((⟨p 0, p 1⟩ : ℂ), p 2))
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  continuous_invFun := by
    change Continuous (fun p : ℂ × ℝ => sourceArchSpatialCoordinates.symm p)
    simp_rw [sourceArchSpatialCoordinates_symm_apply]
    fun_prop

instance sourceArchEuclideanHyperbolicVolume_sigmaFinite : SigmaFinite hyperbolicEuclideanVolume := by
  unfold hyperbolicEuclideanVolume hyperbolicDensity
  infer_instance

def sourceArchEuclideanUpperMap (p : EuclideanSpatial) : SourceArchUpperHalfSpace :=
  sourceArchHyperbolicHomeomorph.symm (euclideanToHyperbolic p)

lemma sourceArchEuclideanUpperMap_preserving :
    MeasurePreserving sourceArchEuclideanUpperMap hyperbolicEuclideanVolume
      sourceArchHyperbolicMeasure := by
  refine ⟨sourceArchHyperbolicHomeomorph.symm.measurable.comp euclideanToHyperbolic_measurable, ?_⟩
  rw [sourceArchHyperbolicMeasure, hyperbolicVolume,
    Measure.map_map sourceArchHyperbolicHomeomorph.symm.measurable euclideanToHyperbolic_measurable]
  rfl

lemma sourceArchEuclideanUpperMap_positive (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchEuclideanUpperMap p =
      ((p 0 : ℂ) + Complex.I * (p 1 : ℂ), ⟨p 2, hp⟩) := by
  apply sourceArchHyperbolicHomeomorph.injective
  change sourceArchHyperbolicHomeomorph
    (sourceArchHyperbolicHomeomorph.symm (euclideanToHyperbolic p)) = _
  rw [Homeomorph.apply_symm_apply, euclideanToHyperbolic_positive p hp]
  rfl

def sourceArchUpperEuclideanMap (p : SourceArchUpperHalfSpace) : EuclideanSpatial :=
  sourceArchSpatialCoordinates.symm (sourceArchUpperEmbedding p)

lemma sourceArchUpperEuclideanMap_continuous : Continuous sourceArchUpperEuclideanMap :=
  sourceArchSpatialHomeomorph.symm.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

lemma sourceArchUpperEuclideanMap_measurableEmbedding :
    MeasurableEmbedding sourceArchUpperEuclideanMap :=
  sourceArchSpatialCoordinates.symm.measurableEmbedding.comp sourceArchUpperEmbedding_measurableEmbedding

lemma sourceArchUpperEuclideanMap_positive (p : SourceArchUpperHalfSpace) :
    0 < sourceArchUpperEuclideanMap p 2 := by
  simpa [sourceArchUpperEuclideanMap, sourceArchSpatialCoordinates_symm_apply,
    sourceArchUpperEmbedding] using p.2.property

lemma sourceArchUpperEuclideanMap_left_inverse (p : SourceArchUpperHalfSpace) :
    sourceArchEuclideanUpperMap (sourceArchUpperEuclideanMap p) = p := by
  apply sourceArchUpperEmbedding_measurableEmbedding.injective
  change sourceArchUpperEmbedding
    (sourceArchHyperbolicHomeomorph.symm (euclideanToHyperbolic (sourceArchUpperEuclideanMap p))) = _
  rw [sourceArchUpperEmbedding_euclidean _ (sourceArchUpperEuclideanMap_positive p)]
  exact sourceArchSpatialCoordinates.apply_symm_apply _

lemma sourceArchUpperEuclideanMap_right_inverse (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchUpperEuclideanMap (sourceArchEuclideanUpperMap p) = p := by
  change sourceArchSpatialCoordinates.symm
    (sourceArchUpperEmbedding (sourceArchHyperbolicHomeomorph.symm (euclideanToHyperbolic p))) = p
  rw [sourceArchUpperEmbedding_euclidean p hp, MeasurableEquiv.symm_apply_apply]

lemma sourceArchUpperEuclideanMap_preserving :
    MeasurePreserving sourceArchUpperEuclideanMap sourceArchHyperbolicMeasure
      hyperbolicEuclideanVolume := by
  refine ⟨sourceArchUpperEuclideanMap_measurableEmbedding.measurable, ?_⟩
  rw [← sourceArchEuclideanUpperMap_preserving.map_eq,
    Measure.map_map sourceArchUpperEuclideanMap_measurableEmbedding.measurable
      sourceArchEuclideanUpperMap_preserving.measurable]
  have he : sourceArchUpperEuclideanMap ∘ sourceArchEuclideanUpperMap =ᵐ[hyperbolicEuclideanVolume] id := by
    filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
    exact sourceArchUpperEuclideanMap_right_inverse p hp
  rw [Measure.map_congr he, Measure.map_id]

end
end ArtinMatthews.SourceArchJacquet
