module

public import ArtinMatthews.SourceKPAdelicTorusWeyl
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

/-! The literal Weyl transport between the two actual algebraically
induced torus carriers, with their right translation actions. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicTorusWeylTransport (s : ℂ) :
    SourceKPAdelicTorusInducedSpace K hζ s ≃ₗ[ℂ] SourceKPAdelicTorusInducedSpace K hζ (-s) where
  toFun f := ⟨fun t => f.val (sourceKPAdelicCoveringTorusWeyl K hζ t), by
    intro h t
    change f.val (sourceKPAdelicCoveringTorusWeyl K hζ (h.val * t)) =
      (sourceKPAdelicTorusInducingCharacter K hζ (-s) h : ℂ) *
        f.val (sourceKPAdelicCoveringTorusWeyl K hζ t)
    rw [map_mul, ← sourceKPAdelicTorusInducingWeyl_val,
      sourceAlgebraicInducedSpace_covariant, sourceKPAdelicTorusInducingRepresentation_apply,
      sourceKPAdelicTorusInducingCharacter_weyl]⟩
  invFun f := ⟨fun t => f.val (sourceKPAdelicCoveringTorusWeyl K hζ t), by
    intro h t
    change f.val (sourceKPAdelicCoveringTorusWeyl K hζ (h.val * t)) =
      (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) *
        f.val (sourceKPAdelicCoveringTorusWeyl K hζ t)
    rw [map_mul, ← sourceKPAdelicTorusInducingWeyl_val,
      sourceAlgebraicInducedSpace_covariant, sourceKPAdelicTorusInducingRepresentation_apply,
      sourceKPAdelicTorusInducingCharacter_weyl, neg_neg]⟩
  left_inv f := by
    apply Subtype.ext
    funext t
    exact congrArg f.val (sourceKPAdelicCoveringTorusWeyl_involutive K hζ t)
  right_inv f := by
    apply Subtype.ext
    funext t
    exact congrArg f.val (sourceKPAdelicCoveringTorusWeyl_involutive K hζ t)
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem sourceKPAdelicTorusWeylTransport_apply (s : ℂ)
    (f : SourceKPAdelicTorusInducedSpace K hζ s) (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicTorusWeylTransport K hζ s f).val t =
      f.val (sourceKPAdelicCoveringTorusWeyl K hζ t) := rfl

theorem sourceKPAdelicTorusWeylTransport_symm_apply (s : ℂ)
    (f : SourceKPAdelicTorusInducedSpace K hζ (-s)) (t : sourceKPAdelicCoveringTorus K hζ) :
    ((sourceKPAdelicTorusWeylTransport K hζ s).symm f).val t =
      f.val (sourceKPAdelicCoveringTorusWeyl K hζ t) := rfl

theorem sourceKPAdelicTorusWeylTransport_one (s : ℂ)
    (f : SourceKPAdelicTorusInducedSpace K hζ s) :
    (sourceKPAdelicTorusWeylTransport K hζ s f).val 1 = f.val 1 := by
  rw [sourceKPAdelicTorusWeylTransport_apply, map_one]

theorem sourceKPAdelicTorusWeylTransport_right (s : ℂ)
    (t : sourceKPAdelicCoveringTorus K hζ) (f : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicTorusWeylTransport K hζ s
      (sourceKPAdelicTorusInducedRepresentation K hζ s t f) =
        sourceKPAdelicTorusInducedRepresentation K hζ (-s)
          (sourceKPAdelicCoveringTorusWeyl K hζ t) (sourceKPAdelicTorusWeylTransport K hζ s f) := by
  apply Subtype.ext
  funext u
  change f.val (sourceKPAdelicCoveringTorusWeyl K hζ u * t) =
    f.val (sourceKPAdelicCoveringTorusWeyl K hζ (u * sourceKPAdelicCoveringTorusWeyl K hζ t))
  rw [map_mul, sourceKPAdelicCoveringTorusWeyl_involutive]

theorem sourceKPAdelicTorusWeylTransport_right_conjugate (s : ℂ)
    (t : sourceKPAdelicCoveringTorus K hζ) (f : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicTorusWeylTransport K hζ s
      (sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicCoveringTorusWeyl K hζ t) f) =
        sourceKPAdelicTorusInducedRepresentation K hζ (-s) t (sourceKPAdelicTorusWeylTransport K hζ s f) := by
  rw [sourceKPAdelicTorusWeylTransport_right, sourceKPAdelicCoveringTorusWeyl_involutive]

theorem sourceKPAdelicTorusWeylTransport_center (s : ℂ) (z : rootsOfUnity 3 K)
    (f : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicTorusWeylTransport K hζ s
      (sourceKPAdelicTorusInducedRepresentation K hζ s
        (sourceKPAdelicTorusInducingCenter K hζ z).val f) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) • sourceKPAdelicTorusWeylTransport K hζ s f := by
  rw [sourceKPAdelicTorusInducedRepresentation_center, map_smul]

end
end ArtinMatthews
