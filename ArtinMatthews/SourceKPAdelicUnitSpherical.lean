module

public import ArtinMatthews.SourceKPAdelicUnitTorus
public import ArtinMatthews.SourceKPAdelicInducedTorus
public import ArtinMatthews.SourceKPAdelicDiagonalCharacter
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

/-! A nonzero right-unit-torus-fixed vector in the actual algebraic induction.
The construction is supported on the product of the inducing subgroup and
unit torus. Smoothness remains a separate topological obligation. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "H" => sourceKPAdelicTorusInducingSubgroup K hζ
local notation "U" => sourceKPAdelicUnitTorus K hζ

theorem sourceKPAdelicUnitTorus_intersection_character (s : ℂ) (h : H) (u : U)
    (he : h.val = u.val) : sourceKPAdelicTorusInducingCharacter K hζ s h = 1 := by
  obtain ⟨a, ha⟩ := sourceKPAdelicUnitTorus_mem K hζ u
  apply sourceKPAdelicParametricRationalCharacter_diagonal_norm_one K hζ s
    (sourceKPAdelicTorusInducingToRationalCube K hζ h) a.val
  · change h.val.val = sourceKPAdelicProjectiveDiagonalLift K hζ a.val
    rw [he, ha]
  · exact sourceKPAdelicUnitIdeles_norm K a

def sourceKPAdelicUnitFactorable (g : T) : Prop := ∃ (h : H) (u : U), g = h.val * u.val

theorem sourceKPAdelicUnitFactor_character_eq (s : ℂ) (h h' : H) (u u' : U)
    (he : h.val * u.val = h'.val * u'.val) :
    sourceKPAdelicTorusInducingCharacter K hζ s h = sourceKPAdelicTorusInducingCharacter K hζ s h' := by
  have hi : (h'⁻¹*h).val = (u'*u⁻¹).val := by
    change h'.val⁻¹*h.val = u'.val*u.val⁻¹
    calc
      _ = h'.val⁻¹ * ((h.val*u.val)*u.val⁻¹) := by group
      _ = h'.val⁻¹ * ((h'.val*u'.val)*u.val⁻¹) := by rw [he]
      _ = _ := by group
  have hc := sourceKPAdelicUnitTorus_intersection_character K hζ s (h'⁻¹*h) (u'*u⁻¹) hi
  rw [map_mul, map_inv] at hc
  have hm := congrArg (fun z => sourceKPAdelicTorusInducingCharacter K hζ s h' * z) hc
  simpa only [mul_inv_cancel_left, mul_one] using hm

def sourceKPAdelicUnitSectionValue (s : ℂ) (g : T) : ℂ :=
  if hg : sourceKPAdelicUnitFactorable K hζ g then
    (sourceKPAdelicTorusInducingCharacter K hζ s hg.choose : ℂ) else 0

theorem sourceKPAdelicUnitSectionValue_factor (s : ℂ) (g : T) (h : H) (u : U)
    (hg : g = h.val*u.val) :
    sourceKPAdelicUnitSectionValue K hζ s g = (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) := by
  have hp : sourceKPAdelicUnitFactorable K hζ g := ⟨h,u,hg⟩
  rw [sourceKPAdelicUnitSectionValue, dite_eq_left hp]
  exact congrArg Units.val (sourceKPAdelicUnitFactor_character_eq K hζ s
    hp.choose h hp.choose_spec.choose u (hp.choose_spec.choose_spec.symm.trans hg))

theorem sourceKPAdelicUnitSectionValue_zero (s : ℂ) (g : T)
    (hg : ¬sourceKPAdelicUnitFactorable K hζ g) : sourceKPAdelicUnitSectionValue K hζ s g = 0 := by
  rw [sourceKPAdelicUnitSectionValue, dite_eq_right hg]

theorem sourceKPAdelicUnitSectionValue_left (s : ℂ) (b : H) (g : T) :
    sourceKPAdelicUnitSectionValue K hζ s (b.val*g) =
      sourceKPAdelicTorusInducingRepresentation K hζ s b (sourceKPAdelicUnitSectionValue K hζ s g) := by
  by_cases hg : sourceKPAdelicUnitFactorable K hζ g
  · obtain ⟨h,u,he⟩ := hg
    have hb : b.val*g = (b*h).val*u.val := by rw [he]; exact (mul_assoc _ _ _).symm
    rw [sourceKPAdelicUnitSectionValue_factor K hζ s _ _ _ hb,
      sourceKPAdelicUnitSectionValue_factor K hζ s _ _ _ he,
      sourceKPAdelicTorusInducingRepresentation_apply, map_mul, Units.val_mul]
  · have hb : ¬sourceKPAdelicUnitFactorable K hζ (b.val*g) := by
      rintro ⟨h,u,he⟩
      apply hg
      refine ⟨b⁻¹*h,u,?_⟩
      change g = (b.val⁻¹*h.val)*u.val
      calc
        g = b.val⁻¹*(b.val*g) := by group
        _ = b.val⁻¹*(h.val*u.val) := by rw [he]
        _ = _ := by group
    rw [sourceKPAdelicUnitSectionValue_zero K hζ s _ hb,
      sourceKPAdelicUnitSectionValue_zero K hζ s _ hg, map_zero]

theorem sourceKPAdelicUnitSectionValue_right (s : ℂ) (g : T) (v : U) :
    sourceKPAdelicUnitSectionValue K hζ s (g*v.val) = sourceKPAdelicUnitSectionValue K hζ s g := by
  by_cases hg : sourceKPAdelicUnitFactorable K hζ g
  · obtain ⟨h,u,he⟩ := hg
    have hv : g*v.val = h.val*(u*v).val := by rw [he]; exact mul_assoc _ _ _
    rw [sourceKPAdelicUnitSectionValue_factor K hζ s _ _ _ hv,
      sourceKPAdelicUnitSectionValue_factor K hζ s _ _ _ he]
  · have hv : ¬sourceKPAdelicUnitFactorable K hζ (g*v.val) := by
      rintro ⟨h,u,he⟩
      apply hg
      refine ⟨h,u*v⁻¹,?_⟩
      change g = h.val*(u.val*v.val⁻¹)
      calc
        g = (g*v.val)*v.val⁻¹ := by group
        _ = (h.val*u.val)*v.val⁻¹ := by rw [he]
        _ = _ := by group
    rw [sourceKPAdelicUnitSectionValue_zero K hζ s _ hv,
      sourceKPAdelicUnitSectionValue_zero K hζ s _ hg]

def sourceKPAdelicUnitSphericalVector (s : ℂ) : SourceKPAdelicTorusInducedSpace K hζ s :=
  ⟨sourceKPAdelicUnitSectionValue K hζ s, sourceKPAdelicUnitSectionValue_left K hζ s⟩

theorem sourceKPAdelicUnitSphericalVector_one (s : ℂ) :
    (sourceKPAdelicUnitSphericalVector K hζ s).val 1 = 1 := by
  change sourceKPAdelicUnitSectionValue K hζ s 1 = 1
  rw [sourceKPAdelicUnitSectionValue_factor K hζ s 1 (1:H) (1:U) (one_mul 1).symm,
    map_one, Units.val_one]

theorem sourceKPAdelicUnitSphericalVector_ne_zero (s : ℂ) :
    sourceKPAdelicUnitSphericalVector K hζ s ≠ 0 := by
  intro h
  have he := congrArg (fun f : SourceKPAdelicTorusInducedSpace K hζ s => f.val 1) h
  rw [sourceKPAdelicUnitSphericalVector_one] at he
  exact one_ne_zero he

theorem sourceKPAdelicUnitSphericalVector_right (s : ℂ) (u : U) :
    sourceKPAdelicTorusInducedRepresentation K hζ s u.val (sourceKPAdelicUnitSphericalVector K hζ s) =
      sourceKPAdelicUnitSphericalVector K hζ s := by
  apply Subtype.ext
  funext g
  exact sourceKPAdelicUnitSectionValue_right K hζ s g u

theorem sourceKPAdelicUnitSphericalVector_support (s : ℂ) :
    Function.support (sourceKPAdelicUnitSphericalVector K hζ s).val ⊆
      {g | sourceKPAdelicUnitFactorable K hζ g} := by
  intro g hg
  by_contra hn
  exact hg (sourceKPAdelicUnitSectionValue_zero K hζ s g hn)

end
end ArtinMatthews
