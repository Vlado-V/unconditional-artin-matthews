module

public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPArchRadialMeasure
public import ArtinMatthews.SourceKPRadialHighFlow
public import ArtinMatthews.QuotientSectionScaling
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

/-! The literal full-frame radial map scales the actual archimedean Haar measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance : MeasurableSpace (SourceKPArchSymmetricSpace K hζ) := borel _
local instance : BorelSpace (SourceKPArchSymmetricSpace K hζ) := ⟨rfl⟩

def sourceKPArchSymmetricRadialHomeomorph (t : ℝ) :
    SourceKPArchSymmetricSpace K hζ ≃ₜ SourceKPArchSymmetricSpace K hζ :=
  (sourceKPArchSymmetricHomeomorph K hζ).trans
    ((sourceKPArchRadialPointHomeomorph K t).trans (sourceKPArchSymmetricHomeomorph K hζ).symm)

theorem sourceKPArchSymmetricRadial_mk (t : ℝ) (g : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchSymmetricRadialHomeomorph K hζ t (QuotientGroup.mk g) =
      QuotientGroup.mk (sourceKPArchRadialFlow K hζ t g) := by
  apply (sourceKPArchSymmetricHomeomorph K hζ).injective
  simp only [sourceKPArchSymmetricRadialHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply]
  change sourceKPArchRadialPoint K t (sourceKPArchGramCoordinates K hζ g) =
    sourceKPArchGramCoordinates K hζ (sourceKPArchRadialFlow K hζ t g)
  exact (sourceKPArchRadialFlow_coordinates K hζ t g).symm

theorem sourceKPArchSymmetricRadial_map_measure (t : ℝ) :
    Measure.map (sourceKPArchSymmetricRadialHomeomorph K hζ t)
      (sourceKPArchSymmetricHyperbolicMeasure K hζ) =
        ENNReal.ofReal (sourceKPRadialHeightScale K t) •
          sourceKPArchSymmetricHyperbolicMeasure K hζ := by
  rw [sourceKPArchSymmetricHyperbolicMeasure, Measure.map_map
    (sourceKPArchSymmetricRadialHomeomorph K hζ t).measurable
    (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable]
  have he : (sourceKPArchSymmetricRadialHomeomorph K hζ t) ∘
      (sourceKPArchSymmetricHomeomorph K hζ).symm =
      (sourceKPArchSymmetricHomeomorph K hζ).symm ∘ sourceKPArchRadialPoint K t := by
    funext p
    simp only [sourceKPArchSymmetricRadialHomeomorph, Homeomorph.trans_apply,
      Homeomorph.apply_symm_apply, Function.comp_apply]
    rfl
  rw [he, ← Measure.map_map (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable
    (sourceKPArchRadialPoint_continuous K t).measurable,
    sourceKPArchRadialPoint_map_hyperbolicMeasure,
    Measure.map_smul _ (sourceKPArchSymmetricHomeomorph K hζ).symm.measurable.aemeasurable]
  rfl

theorem sourceKPArchRadialFlow_continuous_fixed (t : ℝ) :
    Continuous (sourceKPArchRadialFlow K hζ t) := by
  have harg : Continuous (fun g : PGL(2, InfiniteAdeleRing K) => (t,g)) :=
    continuous_const.prodMk continuous_id
  have h := (sourceKPArchRadialFlow_continuous K hζ).comp harg
  simpa only [Function.comp_def] using h

def sourceKPArchRadialHomeomorph (t : ℝ) :
    PGL(2, InfiniteAdeleRing K) ≃ₜ PGL(2, InfiniteAdeleRing K) where
  toFun := sourceKPArchRadialFlow K hζ t
  invFun := sourceKPArchRadialFlow K hζ (-t)
  left_inv g := by rw [sourceKPArchRadialFlow_add, neg_add_cancel, sourceKPArchRadialFlow_zero]
  right_inv g := by rw [sourceKPArchRadialFlow_add, add_neg_cancel, sourceKPArchRadialFlow_zero]
  continuous_toFun := sourceKPArchRadialFlow_continuous_fixed K hζ t
  continuous_invFun := sourceKPArchRadialFlow_continuous_fixed K hζ (-t)

theorem sourceKPArchRadialFlow_map_haar (t : ℝ) :
    Measure.map (sourceKPArchRadialFlow K hζ t) (sourceKPArchHaar K hζ) =
      ENNReal.ofReal (sourceKPRadialHeightScale K t) • sourceKPArchHaar K hζ := by
  have hbase : MeasurePreserving (sourceKPArchSymmetricRadialHomeomorph K hζ t)
      (sourceKPArchSymmetricHyperbolicMeasure K hζ)
      (ENNReal.ofReal (sourceKPRadialHeightScale K t) •
        sourceKPArchSymmetricHyperbolicMeasure K hζ) :=
    ⟨(sourceKPArchSymmetricRadialHomeomorph K hζ t).measurable,
      sourceKPArchSymmetricRadial_map_measure K hζ t⟩
  have h := quotientSectionMeasure_equivariant_transport
    (sourceKPArchBaseCompactSubgroup K hζ) (sourceKPArchFrameSection K hζ)
    (sourceKPArchFrameSection_rightInverse K hζ) (sourceKPArchFrameSection_continuous K hζ)
    (sourceKPArchSymmetricHyperbolicMeasure K hζ)
    (ENNReal.ofReal (sourceKPRadialHeightScale K t) • sourceKPArchSymmetricHyperbolicMeasure K hζ)
    (sourceKPArchCompactHaar K hζ) (sourceKPArchRadialFlow K hζ t)
    (sourceKPArchRadialHomeomorph K hζ t).continuous
    (fun g k => sourceKPArchRadialFlow_compact K hζ t g k.val k.property)
    (sourceKPArchSymmetricRadialHomeomorph K hζ t) hbase
    (fun g => (sourceKPArchSymmetricRadial_mk K hζ t g).symm)
  rw [quotientSectionMeasure_smul _ _ (sourceKPArchFrameSection_continuous K hζ)] at h
  exact h.map_eq

theorem sourceKPArchRadialFlow_image_haar (t : ℝ)
    (A : Set (PGL(2, InfiniteAdeleRing K))) (hA : MeasurableSet A) :
    sourceKPArchHaar K hζ (sourceKPArchRadialFlow K hζ t '' A) =
      ENNReal.ofReal (sourceKPRadialHeightScale K (-t)) * sourceKPArchHaar K hζ A := by
  have h := congrArg (fun μ : Measure (PGL(2, InfiniteAdeleRing K)) => μ A)
    (sourceKPArchRadialFlow_map_haar K hζ (-t))
  rw [Measure.map_apply (sourceKPArchRadialFlow_continuous_fixed K hζ (-t)).measurable hA,
    Measure.smul_apply] at h
  have hp : sourceKPArchRadialFlow K hζ (-t) ⁻¹' A =
      sourceKPArchRadialFlow K hζ t '' A := by
    exact ((sourceKPArchRadialHomeomorph K hζ t).image_eq_preimage_symm A).symm
  simpa only [hp, smul_eq_mul] using h

end
end ArtinMatthews
