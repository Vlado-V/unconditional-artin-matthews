module

public import ArtinMatthews.SourceKPAdelicInducedTorus
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Weyl conjugation on the actual covering torus and its inducing
subgroup. The central cubic phase is fixed by this involution. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicWeylConjugation_involutive :
    Function.Involutive (fun g : SourceKPAdelicProjective K hζ =>
      sourceKPAdelicProjectiveWeyl K hζ * g * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹) := by
  intro g
  let W := sourceKPAdelicProjectiveWeyl K hζ
  have hW : W * W = 1 := sourceKPAdelicProjectiveWeyl_square K hζ
  have hi : W⁻¹ = W := inv_eq_of_mul_eq_one_right hW
  change W * (W * g * W⁻¹) * W⁻¹ = g
  rw [hi]
  calc
    W * (W * g * W) * W = (W * W) * g * (W * W) := by group
    _ = g := by rw [hW, one_mul, mul_one]

theorem sourceKPAdelicCoveringTorus_weyl_mem (t : sourceKPAdelicCoveringTorus K hζ) :
    sourceKPAdelicProjectiveWeyl K hζ * t.val * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ ∈
      sourceKPAdelicCoveringTorus K hζ := by
  obtain ⟨z, a, ht⟩ := (sourceKPAdelicCoveringTorus_mem_iff K hζ t.val).mp t.property
  rw [ht, (sourceKPAdelicProjectiveCenter_commute K hζ z
    (sourceKPAdelicProjectiveWeyl K hζ)).symm.left_comm,
    mul_assoc, sourceKPAdelicProjectiveWeyl_conj_diagonal]
  exact (sourceKPAdelicCoveringTorus K hζ).mul_mem
    (sourceKPAdelicCoveringTorus_center_mem K hζ z)
    (sourceKPAdelicCoveringTorus_diagonal_mem K hζ a⁻¹)

def sourceKPAdelicCoveringTorusWeyl :
    sourceKPAdelicCoveringTorus K hζ ≃* sourceKPAdelicCoveringTorus K hζ where
  toFun t := ⟨sourceKPAdelicProjectiveWeyl K hζ * t.val *
    (sourceKPAdelicProjectiveWeyl K hζ)⁻¹, sourceKPAdelicCoveringTorus_weyl_mem K hζ t⟩
  invFun t := ⟨sourceKPAdelicProjectiveWeyl K hζ * t.val *
    (sourceKPAdelicProjectiveWeyl K hζ)⁻¹, sourceKPAdelicCoveringTorus_weyl_mem K hζ t⟩
  left_inv t := Subtype.ext (sourceKPAdelicWeylConjugation_involutive K hζ t.val)
  right_inv t := Subtype.ext (sourceKPAdelicWeylConjugation_involutive K hζ t.val)
  map_mul' t u := by
    apply Subtype.ext
    change sourceKPAdelicProjectiveWeyl K hζ * (t.val * u.val) *
      (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ =
        (sourceKPAdelicProjectiveWeyl K hζ * t.val * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹) *
          (sourceKPAdelicProjectiveWeyl K hζ * u.val * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹)
    group

theorem sourceKPAdelicCoveringTorusWeyl_val (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicCoveringTorusWeyl K hζ t).val =
      sourceKPAdelicProjectiveWeyl K hζ * t.val * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ := rfl

theorem sourceKPAdelicCoveringTorusWeyl_involutive :
    Function.Involutive (sourceKPAdelicCoveringTorusWeyl K hζ) :=
  (sourceKPAdelicCoveringTorusWeyl K hζ).left_inv

theorem sourceKPAdelicCoveringTorusWeyl_center (z : rootsOfUnity 3 K) :
    sourceKPAdelicCoveringTorusWeyl K hζ
      ⟨sourceKPAdelicProjectiveCenter K hζ z, sourceKPAdelicCoveringTorus_center_mem K hζ z⟩ =
      ⟨sourceKPAdelicProjectiveCenter K hζ z, sourceKPAdelicCoveringTorus_center_mem K hζ z⟩ := by
  apply Subtype.ext
  change sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicProjectiveCenter K hζ z *
    (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ = sourceKPAdelicProjectiveCenter K hζ z
  rw [(sourceKPAdelicProjectiveCenter_commute K hζ z
    (sourceKPAdelicProjectiveWeyl K hζ)).symm.eq, mul_inv_cancel_right]

theorem sourceKPAdelicTorusInducing_weyl_mem (h : sourceKPAdelicTorusInducingSubgroup K hζ) :
    sourceKPAdelicCoveringTorusWeyl K hζ h.val ∈ sourceKPAdelicTorusInducingSubgroup K hζ :=
  (sourceKPAdelicRationalCubeWeyl K hζ
    (sourceKPAdelicTorusInducingToRationalCube K hζ h)).property

def sourceKPAdelicTorusInducingWeyl :
    sourceKPAdelicTorusInducingSubgroup K hζ ≃* sourceKPAdelicTorusInducingSubgroup K hζ where
  toFun h := ⟨sourceKPAdelicCoveringTorusWeyl K hζ h.val,
    sourceKPAdelicTorusInducing_weyl_mem K hζ h⟩
  invFun h := ⟨sourceKPAdelicCoveringTorusWeyl K hζ h.val,
    sourceKPAdelicTorusInducing_weyl_mem K hζ h⟩
  left_inv h := Subtype.ext (sourceKPAdelicCoveringTorusWeyl_involutive K hζ h.val)
  right_inv h := Subtype.ext (sourceKPAdelicCoveringTorusWeyl_involutive K hζ h.val)
  map_mul' h k := Subtype.ext (map_mul (sourceKPAdelicCoveringTorusWeyl K hζ) h.val k.val)

theorem sourceKPAdelicTorusInducingWeyl_val (h : sourceKPAdelicTorusInducingSubgroup K hζ) :
    (sourceKPAdelicTorusInducingWeyl K hζ h).val =
      sourceKPAdelicCoveringTorusWeyl K hζ h.val := rfl

theorem sourceKPAdelicTorusInducingWeyl_involutive :
    Function.Involutive (sourceKPAdelicTorusInducingWeyl K hζ) :=
  (sourceKPAdelicTorusInducingWeyl K hζ).left_inv

theorem sourceKPAdelicTorusInducingWeyl_toRational (h : sourceKPAdelicTorusInducingSubgroup K hζ) :
    sourceKPAdelicTorusInducingToRationalCube K hζ (sourceKPAdelicTorusInducingWeyl K hζ h) =
      sourceKPAdelicRationalCubeWeyl K hζ (sourceKPAdelicTorusInducingToRationalCube K hζ h) := rfl

theorem sourceKPAdelicTorusInducingCharacter_weyl (s : ℂ)
    (h : sourceKPAdelicTorusInducingSubgroup K hζ) :
    sourceKPAdelicTorusInducingCharacter K hζ s (sourceKPAdelicTorusInducingWeyl K hζ h) =
      sourceKPAdelicTorusInducingCharacter K hζ (-s) h :=
  (DFunLike.congr_fun (sourceKPAdelicParametricRationalCharacter_weyl K hζ s)
    (sourceKPAdelicTorusInducingToRationalCube K hζ h)).symm

theorem sourceKPAdelicTorusInducingWeyl_center (z : rootsOfUnity 3 K) :
    sourceKPAdelicTorusInducingWeyl K hζ (sourceKPAdelicTorusInducingCenter K hζ z) =
      sourceKPAdelicTorusInducingCenter K hζ z := by
  apply Subtype.ext
  have he : (sourceKPAdelicTorusInducingCenter K hζ z).val =
      ⟨sourceKPAdelicProjectiveCenter K hζ z, sourceKPAdelicCoveringTorus_center_mem K hζ z⟩ :=
    Subtype.ext (sourceKPAdelicTorusInducingCenter_val K hζ z)
  change sourceKPAdelicCoveringTorusWeyl K hζ
    (sourceKPAdelicTorusInducingCenter K hζ z).val = (sourceKPAdelicTorusInducingCenter K hζ z).val
  rw [he, sourceKPAdelicCoveringTorusWeyl_center]

end
end ArtinMatthews
