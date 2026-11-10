module

public import ArtinMatthews.SourceKPArchHyperbolicMeasure
public import ArtinMatthews.SourceHyperbolicProductMeasure
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

namespace ArtinMatthews
open NumberField MeasureTheory SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

abbrev SourceKPArchPositiveCoordinates := {p : ProductSpace (InfinitePlace K) // p ∈ productUpper (InfinitePlace K)}

def sourceKPArchPositiveToUpper (p : SourceKPArchPositiveCoordinates K) : SourceKPArchUpperHalfSpace K :=
  fun v => ((p.val v 0 : ℂ) + Complex.I * (p.val v 1 : ℂ),
    ⟨p.val v 2,p.prop v (Set.mem_univ v)⟩)

omit [NumberField K] in
theorem sourceKPArchPositiveToUpper_eq (p : SourceKPArchPositiveCoordinates K) :
    sourceKPArchPositiveToUpper K p = sourceKPArchEuclideanUpperMap K p.val := by
  funext v
  exact (sourceKPArchEuclideanUpperMap_positive K p.val
    (fun w => p.prop w (Set.mem_univ w)) v).symm

omit [NumberField K] in
theorem sourceKPArchPositiveToUpper_continuous : Continuous (sourceKPArchPositiveToUpper K) := by
  apply continuous_pi
  intro v
  have hv : Continuous (fun p : SourceKPArchPositiveCoordinates K => p.val v) :=
    (continuous_apply v).comp continuous_subtype_val
  have h0 : Continuous (fun p : SourceKPArchPositiveCoordinates K => (p.val v 0 : ℂ)) :=
    Complex.continuous_ofReal.comp ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 0).comp hv)
  have h1 : Continuous (fun p : SourceKPArchPositiveCoordinates K => (p.val v 1 : ℂ)) :=
    Complex.continuous_ofReal.comp ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 1).comp hv)
  have h2 : Continuous (fun p : SourceKPArchPositiveCoordinates K => p.val v 2) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2).comp hv
  exact (h0.add (continuous_const.mul h1)).prodMk (h2.subtype_mk _)

def sourceKPArchPositiveHomeomorph : SourceKPArchUpperHalfSpace K ≃ₜ SourceKPArchPositiveCoordinates K where
  toFun p := ⟨sourceKPArchUpperEuclideanMap K p, fun v _ => sourceArchUpperEuclideanMap_positive (p v)⟩
  invFun := sourceKPArchPositiveToUpper K
  left_inv p := by
    rw [sourceKPArchPositiveToUpper_eq]
    exact sourceKPArchUpperEuclideanMap_left_inverse K p
  right_inv p := by
    apply Subtype.ext
    change sourceKPArchUpperEuclideanMap K (sourceKPArchPositiveToUpper K p) = p.val
    rw [sourceKPArchPositiveToUpper_eq]
    exact sourceKPArchUpperEuclideanMap_right_inverse K p.val (fun v => p.prop v (Set.mem_univ v))
  continuous_toFun := (sourceKPArchUpperEuclideanMap_continuous K).subtype_mk _
  continuous_invFun := sourceKPArchPositiveToUpper_continuous K

omit [NumberField K] in
theorem sourceKPArchPositiveHomeomorph_apply (p : SourceKPArchUpperHalfSpace K) :
    (sourceKPArchPositiveHomeomorph K p).val = sourceKPArchUpperEuclideanMap K p := rfl

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

def sourceKPArchLpCoordinates :
    Lp F 2 (productVolume (InfinitePlace K)) ≃ₗᵢ[ℂ]
      Lp F 2 (sourceKPArchHyperbolicMeasure K) := by
  let T := Lp.compMeasurePreservingₗᵢ ℂ (sourceKPArchUpperEuclideanMap K)
    (sourceKPArchUpperEuclideanMap_preserving K) (E := F) (p := 2)
  apply LinearIsometryEquiv.ofSurjective T
  intro f
  refine ⟨Lp.compMeasurePreserving (sourceKPArchEuclideanUpperMap K)
    (sourceKPArchEuclideanUpperMap_preserving K) f, ?_⟩
  change Lp.compMeasurePreserving (sourceKPArchUpperEuclideanMap K)
      (sourceKPArchUpperEuclideanMap_preserving K)
      (Lp.compMeasurePreserving (sourceKPArchEuclideanUpperMap K)
        (sourceKPArchEuclideanUpperMap_preserving K) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : sourceKPArchEuclideanUpperMap K ∘ sourceKPArchUpperEuclideanMap K = id := by
    funext p
    exact sourceKPArchUpperEuclideanMap_left_inverse K p
  simpa only [he] using Lp.compMeasurePreserving_id_apply f

theorem sourceKPArchLpCoordinates_coe (f : Lp F 2 (productVolume (InfinitePlace K))) :
    (sourceKPArchLpCoordinates K F f : SourceKPArchUpperHalfSpace K → F) =ᵐ[sourceKPArchHyperbolicMeasure K]
      fun p => f (sourceKPArchUpperEuclideanMap K p) :=
  Lp.coeFn_compMeasurePreserving f (sourceKPArchUpperEuclideanMap_preserving K)

end
end ArtinMatthews
