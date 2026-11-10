module

public import ArtinMatthews.SourceFiniteUnitaryProjection
public import ArtinMatthews.SourceKPCubicCompactAction
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAdelicUnitNorm
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

/-! The genuine L² projector on the actual compact quotient.
The ambient left-invariant measure supplies center invariance. -/

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing BigOperators ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceKPCompactCubicCenter_fintype : Fintype (rootsOfUnity 3 K) := Fintype.ofFinite _

include hζ in
omit [NumberField K] in
theorem sourceKPCubicCenter_card_three : Fintype.card (rootsOfUnity 3 K) = 3 := by
  rw [← Nat.card_eq_fintype_card]
  exact (IsPrimitiveRoot.pow (by decide : 0 < 12) hζ (by decide : 12 = 4 * 3)).card_rootsOfUnity

variable (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant]

def sourceKPCompactCubicL2Pullback (z : rootsOfUnity 3 K) :
    SourceKPAutomorphicL2 K hζ μ →ₗᵢ[ℂ] SourceKPAutomorphicL2 K hζ μ :=
  Lp.compMeasurePreservingₗᵢ ℂ ((fun x : (SourceKPAutomorphicCompactLevel K hζ) => z⁻¹ • x) : (SourceKPAutomorphicCompactLevel K hζ) → (SourceKPAutomorphicCompactLevel K hζ)) (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z⁻¹ μ)

def sourceKPCompactCubicL2Representation : rootsOfUnity 3 K →* (SourceKPAutomorphicL2 K hζ μ →L[ℂ] SourceKPAutomorphicL2 K hζ μ) where
  toFun z := (sourceKPCompactCubicL2Pullback K hζ μ z).toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    change Lp.compMeasurePreserving ((fun x : (SourceKPAutomorphicCompactLevel K hζ) => (1 : rootsOfUnity 3 K)⁻¹ • x) : (SourceKPAutomorphicCompactLevel K hζ) → (SourceKPAutomorphicCompactLevel K hζ)) _ f = f
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving f (sourceKPAutomorphicCompactMeasure_center_preserving K hζ (1 : rootsOfUnity 3 K)⁻¹ μ)] with x hx
    simpa only [inv_one, one_smul, Function.comp_apply] using hx
  map_mul' z w := by
    apply ContinuousLinearMap.ext
    intro f
    change Lp.compMeasurePreserving ((fun x : (SourceKPAutomorphicCompactLevel K hζ) => (z * w)⁻¹ • x) : (SourceKPAutomorphicCompactLevel K hζ) → (SourceKPAutomorphicCompactLevel K hζ)) _ f =
      Lp.compMeasurePreserving ((fun x : (SourceKPAutomorphicCompactLevel K hζ) => z⁻¹ • x) : (SourceKPAutomorphicCompactLevel K hζ) → (SourceKPAutomorphicCompactLevel K hζ)) _
        (Lp.compMeasurePreserving ((fun x : (SourceKPAutomorphicCompactLevel K hζ) => w⁻¹ • x) : (SourceKPAutomorphicCompactLevel K hζ) → (SourceKPAutomorphicCompactLevel K hζ)) _ f)
    simpa only [Function.comp_def, _root_.mul_inv_rev, mul_smul] using
      Lp.compMeasurePreserving_comp_apply f (sourceKPAutomorphicCompactMeasure_center_preserving K hζ w⁻¹ μ) (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z⁻¹ μ)

theorem sourceKPCompactCubicL2Representation_norm (z : rootsOfUnity 3 K) (f : SourceKPAutomorphicL2 K hζ μ) :
    ‖sourceKPCompactCubicL2Representation K hζ μ z f‖ = ‖f‖ :=
  (sourceKPCompactCubicL2Pullback K hζ μ z).norm_map f

theorem sourceKPCompactCubicL2Representation_ae (z : rootsOfUnity 3 K) (f : SourceKPAutomorphicL2 K hζ μ) :
    (sourceKPCompactCubicL2Representation K hζ μ z f : (SourceKPAutomorphicCompactLevel K hζ) → ℂ) =ᵐ[sourceKPAutomorphicCompactMeasure K hζ μ]
      fun x => f (z⁻¹ • x) :=
  Lp.coeFn_compMeasurePreserving f (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z⁻¹ μ)

def sourceKPCompactGenuineL2Representation : rootsOfUnity 3 K →* (SourceKPAutomorphicL2 K hζ μ →L[ℂ] SourceKPAutomorphicL2 K hζ μ) where
  toFun z := (sourceKPAdelicCentralComplex K hζ z : ℂ) •
    sourceKPCompactCubicL2Representation K hζ μ z
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    change (sourceKPAdelicCentralComplex K hζ 1 : ℂ) •
      sourceKPCompactCubicL2Representation K hζ μ 1 f = f
    simp only [map_one, Units.val_one, one_apply_eq_self, one_smul]
  map_mul' z w := by
    apply ContinuousLinearMap.ext
    intro f
    change (sourceKPAdelicCentralComplex K hζ (z * w) : ℂ) •
      sourceKPCompactCubicL2Representation K hζ μ (z * w) f =
        (sourceKPAdelicCentralComplex K hζ z : ℂ) •
          sourceKPCompactCubicL2Representation K hζ μ z
            ((sourceKPAdelicCentralComplex K hζ w : ℂ) • sourceKPCompactCubicL2Representation K hζ μ w f)
    rw [map_mul, Units.val_mul, map_mul]
    simp only [mul_apply_eq_comp, map_smul, smul_smul]

theorem sourceKPCompactGenuineL2Representation_norm (z : rootsOfUnity 3 K) (f : SourceKPAutomorphicL2 K hζ μ) :
    ‖sourceKPCompactGenuineL2Representation K hζ μ z f‖ = ‖f‖ := by
  change ‖(sourceKPAdelicCentralComplex K hζ z : ℂ) •
    sourceKPCompactCubicL2Representation K hζ μ z f‖ = ‖f‖
  rw [norm_smul, sourceKPAdelicCentralComplex_norm, one_mul,
    sourceKPCompactCubicL2Representation_norm]

def sourceKPCompactGenuineL2Subspace : Submodule ℂ (SourceKPAutomorphicL2 K hζ μ) :=
  sourceFiniteContinuousInvariants (sourceKPCompactGenuineL2Representation K hζ μ)

theorem sourceKPCompactGenuineL2Subspace_mem (f : SourceKPAutomorphicL2 K hζ μ) :
    f ∈ sourceKPCompactGenuineL2Subspace K hζ μ ↔
      ∀ z : rootsOfUnity 3 K, sourceKPCompactCubicL2Representation K hζ μ z f =
        (sourceKPAdelicCentralComplex K hζ z : ℂ)⁻¹ • f := by
  rw [sourceKPCompactGenuineL2Subspace, sourceFiniteContinuousInvariants_mem]
  constructor
  · intro h z
    have hz := h z
    change (sourceKPAdelicCentralComplex K hζ z : ℂ) •
      sourceKPCompactCubicL2Representation K hζ μ z f = f at hz
    have hc := (sourceKPAdelicCentralComplex K hζ z).ne_zero
    calc
      _ = (sourceKPAdelicCentralComplex K hζ z : ℂ)⁻¹ •
          ((sourceKPAdelicCentralComplex K hζ z : ℂ) •
            sourceKPCompactCubicL2Representation K hζ μ z f) := by simp [smul_smul, hc]
      _ = _ := congrArg (fun v => (sourceKPAdelicCentralComplex K hζ z : ℂ)⁻¹ • v) hz
  · intro h z
    change (sourceKPAdelicCentralComplex K hζ z : ℂ) •
      sourceKPCompactCubicL2Representation K hζ μ z f = f
    rw [h z, smul_smul, mul_inv_cancel₀ (sourceKPAdelicCentralComplex K hζ z).ne_zero, one_smul]

theorem sourceKPCompactGenuineL2Subspace_mem_ae (f : SourceKPAutomorphicL2 K hζ μ) :
    f ∈ sourceKPCompactGenuineL2Subspace K hζ μ ↔
      ∀ z : rootsOfUnity 3 K, (fun x : (SourceKPAutomorphicCompactLevel K hζ) => f (z • x)) =ᵐ[sourceKPAutomorphicCompactMeasure K hζ μ]
        fun x => (sourceKPAdelicCentralComplex K hζ z : ℂ) * f x := by
  constructor
  · intro hf z
    have hu := (sourceKPCompactGenuineL2Subspace_mem K hζ μ f).mp hf z⁻¹
    simp only [map_inv, Units.val_inv_eq_inv_val, inv_inv] at hu
    have hp := sourceKPCompactCubicL2Representation_ae K hζ μ z⁻¹ f
    rw [hu] at hp
    have h := hp.symm.trans (Lp.coeFn_smul (sourceKPAdelicCentralComplex K hζ z : ℂ) f)
    filter_upwards [h] with x hx
    simpa only [inv_inv, Pi.smul_apply, smul_eq_mul] using hx
  · intro hf
    apply (sourceKPCompactGenuineL2Subspace_mem K hζ μ f).mpr
    intro z
    apply Lp.ext
    have hp := sourceKPCompactCubicL2Representation_ae K hζ μ z f
    have hz := hf z⁻¹
    simp only [map_inv, Units.val_inv_eq_inv_val] at hz
    exact hp.trans (hz.trans (Lp.coeFn_smul (sourceKPAdelicCentralComplex K hζ z : ℂ)⁻¹ f).symm)

theorem sourceKPCompactGenuineL2Subspace_isClosed :
    IsClosed (sourceKPCompactGenuineL2Subspace K hζ μ : Set (SourceKPAutomorphicL2 K hζ μ)) :=
  sourceFiniteContinuousInvariants_isClosed _

instance sourceKPCompactGenuineL2Subspace_complete :
    CompleteSpace (sourceKPCompactGenuineL2Subspace K hζ μ) :=
  (sourceKPCompactGenuineL2Subspace_isClosed K hζ μ).completeSpace_coe

def sourceKPCompactGenuineL2Projector : SourceKPAutomorphicL2 K hζ μ →L[ℂ] SourceKPAutomorphicL2 K hζ μ :=
  sourceFiniteAverage (sourceKPCompactGenuineL2Representation K hζ μ)

theorem sourceKPCompactGenuineL2Projector_apply (f : SourceKPAutomorphicL2 K hζ μ) :
    sourceKPCompactGenuineL2Projector K hζ μ f = (Fintype.card (rootsOfUnity 3 K) : ℂ)⁻¹ •
      ∑ z : rootsOfUnity 3 K, (sourceKPAdelicCentralComplex K hζ z : ℂ) •
        sourceKPCompactCubicL2Representation K hζ μ z f :=
  sourceFiniteAverage_apply _ f

theorem sourceKPCompactGenuineL2Projector_range :
    (sourceKPCompactGenuineL2Projector K hζ μ).range = sourceKPCompactGenuineL2Subspace K hζ μ :=
  sourceFiniteAverage_range _

theorem sourceKPCompactGenuineL2Projector_idempotent :
    IsIdempotentElem (sourceKPCompactGenuineL2Projector K hζ μ) :=
  sourceFiniteAverage_idempotent _

theorem sourceKPCompactGenuineL2Projector_eq_starProjection :
    sourceKPCompactGenuineL2Projector K hζ μ =
      (sourceKPCompactGenuineL2Subspace K hζ μ).starProjection :=
  sourceFiniteAverage_eq_starProjection _ (sourceKPCompactGenuineL2Representation_norm K hζ μ)

theorem sourceKPCompactGenuineL2Projector_norm_le : ‖sourceKPCompactGenuineL2Projector K hζ μ‖ ≤ 1 :=
  sourceFiniteAverage_norm_le _ (sourceKPCompactGenuineL2Representation_norm K hζ μ)

theorem sourceKPCompactGenuineL2Projector_isSymmetric :
    (sourceKPCompactGenuineL2Projector K hζ μ).toLinearMap.IsSymmetric :=
  sourceFiniteAverage_isSymmetric _ (sourceKPCompactGenuineL2Representation_norm K hζ μ)

theorem sourceKPCompactGenuineL2Projector_fixed_iff (f : SourceKPAutomorphicL2 K hζ μ) :
    sourceKPCompactGenuineL2Projector K hζ μ f = f ↔ f ∈ sourceKPCompactGenuineL2Subspace K hζ μ :=
  (sourceFiniteAverage_isProj (sourceKPCompactGenuineL2Representation K hζ μ)).mem_iff_map_id.symm


theorem sourceKPCompactGenuineL2Projector_apply_three (f : SourceKPAutomorphicL2 K hζ μ) :
    sourceKPCompactGenuineL2Projector K hζ μ f = (3 : ℂ)⁻¹ •
      ∑ z : rootsOfUnity 3 K, (sourceKPAdelicCentralComplex K hζ z : ℂ) •
        sourceKPCompactCubicL2Representation K hζ μ z f := by
  simpa only [sourceKPCubicCenter_card_three K hζ, Nat.cast_ofNat] using
    sourceKPCompactGenuineL2Projector_apply K hζ μ f

abbrev SourceKPGenuineAutomorphicL2 :=
  ↥(sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ))

def sourceKPGenuineAutomorphicL2Projector :
    SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ) →L[ℂ]
      SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ) :=
  sourceKPCompactGenuineL2Projector K hζ (sourceKPArchHaar K hζ)

end
end ArtinMatthews
