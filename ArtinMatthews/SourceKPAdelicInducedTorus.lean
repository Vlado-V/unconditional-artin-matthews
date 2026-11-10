module

public import ArtinMatthews.SourceKPAdelicParametricRational
public import ArtinMatthews.SourceKPAdelicCoveringTorus
public import ArtinMatthews.SourceAlgebraicInduction
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

/-! Algebraic induction on the actual full adelic covering torus.
The subgroup-supported section proves nonvanishing. Smoothness and
restricted-tensor realization require further constructions. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicTorusInducingSubgroup : Subgroup (sourceKPAdelicCoveringTorus K hζ) :=
  (sourceKPAdelicRationalCubeTorus K hζ).comap (sourceKPAdelicCoveringTorus K hζ).subtype

def sourceKPAdelicTorusInducingToRationalCube :
    sourceKPAdelicTorusInducingSubgroup K hζ →* sourceKPAdelicRationalCubeTorus K hζ where
  toFun h := ⟨h.val.val, h.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

def sourceKPAdelicRationalCubeToInducing :
    sourceKPAdelicRationalCubeTorus K hζ →* sourceKPAdelicTorusInducingSubgroup K hζ where
  toFun h := ⟨⟨h.val, sourceKPAdelicRationalCubeTorus_le_coveringTorus K hζ h.property⟩, h.property⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)

def sourceKPAdelicTorusInducingCharacter (s : ℂ) : sourceKPAdelicTorusInducingSubgroup K hζ →* ℂˣ :=
  (sourceKPAdelicParametricRationalCharacter K hζ s).comp (sourceKPAdelicTorusInducingToRationalCube K hζ)

def sourceKPAdelicTorusInducingRepresentation (s : ℂ) :
    Representation ℂ (sourceKPAdelicTorusInducingSubgroup K hζ) ℂ where
  toFun h := (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro z
    change (sourceKPAdelicTorusInducingCharacter K hζ s 1 : ℂ) * z = z
    rw [map_one, Units.val_one, one_mul]
  map_mul' h k := by
    apply LinearMap.ext
    intro z
    change (sourceKPAdelicTorusInducingCharacter K hζ s (h*k) : ℂ) * z =
      (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) *
        ((sourceKPAdelicTorusInducingCharacter K hζ s k : ℂ) * z)
    rw [map_mul, Units.val_mul, mul_assoc]

theorem sourceKPAdelicTorusInducingRepresentation_apply (s : ℂ)
    (h : sourceKPAdelicTorusInducingSubgroup K hζ) (z : ℂ) :
    sourceKPAdelicTorusInducingRepresentation K hζ s h z =
      (sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ) * z := rfl

abbrev SourceKPAdelicTorusInducedSpace (s : ℂ) :=
  sourceAlgebraicInducedSpace (sourceKPAdelicTorusInducingSubgroup K hζ)
    (sourceKPAdelicTorusInducingRepresentation K hζ s)

def sourceKPAdelicTorusInducedRepresentation (s : ℂ) :
    Representation ℂ (sourceKPAdelicCoveringTorus K hζ) (SourceKPAdelicTorusInducedSpace K hζ s) :=
  sourceAlgebraicInducedRepresentation (sourceKPAdelicTorusInducingSubgroup K hζ)
    (sourceKPAdelicTorusInducingRepresentation K hζ s)

def sourceKPAdelicTorusInducedSection (s : ℂ) : SourceKPAdelicTorusInducedSpace K hζ s :=
  ⟨fun g => if hg : g ∈ sourceKPAdelicTorusInducingSubgroup K hζ then
      (sourceKPAdelicTorusInducingCharacter K hζ s ⟨g, hg⟩ : ℂ) else 0, by
    intro b g
    by_cases hg : g ∈ sourceKPAdelicTorusInducingSubgroup K hζ
    · have hbg := (sourceKPAdelicTorusInducingSubgroup K hζ).mul_mem b.property hg
      simp only [dite_eq_left hbg, dite_eq_left hg, sourceKPAdelicTorusInducingRepresentation_apply]
      change (sourceKPAdelicTorusInducingCharacter K hζ s (b * ⟨g, hg⟩) : ℂ) = _
      rw [map_mul, Units.val_mul]
    · have hbg : b.val * g ∉ sourceKPAdelicTorusInducingSubgroup K hζ := by
        intro h
        apply hg
        have h' := (sourceKPAdelicTorusInducingSubgroup K hζ).mul_mem
          ((sourceKPAdelicTorusInducingSubgroup K hζ).inv_mem b.property) h
        simpa only [inv_mul_cancel_left] using h'
      simp only [dite_eq_right hbg, dite_eq_right hg, sourceKPAdelicTorusInducingRepresentation_apply, mul_zero]⟩

theorem sourceKPAdelicTorusInducedSection_one (s : ℂ) :
    (sourceKPAdelicTorusInducedSection K hζ s).val 1 = 1 := by
  change (if h : (1 : sourceKPAdelicCoveringTorus K hζ) ∈ sourceKPAdelicTorusInducingSubgroup K hζ then
    (sourceKPAdelicTorusInducingCharacter K hζ s ⟨1, h⟩ : ℂ) else 0) = 1
  rw [dite_eq_left (sourceKPAdelicTorusInducingSubgroup K hζ).one_mem]
  change (sourceKPAdelicTorusInducingCharacter K hζ s 1 : ℂ) = 1
  rw [map_one, Units.val_one]

theorem sourceKPAdelicTorusInducedSection_ne_zero (s : ℂ) :
    sourceKPAdelicTorusInducedSection K hζ s ≠ 0 := by
  intro h
  have he := congrArg (fun f : SourceKPAdelicTorusInducedSpace K hζ s => f.val 1) h
  rw [sourceKPAdelicTorusInducedSection_one] at he
  exact one_ne_zero he

def sourceKPAdelicTorusInducingCube (b : sourceKPAdelicCubeTorus K hζ) :
    sourceKPAdelicTorusInducingSubgroup K hζ :=
  sourceKPAdelicRationalCubeToInducing K hζ (sourceKPAdelicRationalCubeFromCube K hζ b)

theorem sourceKPAdelicTorusInducingCube_val (b : sourceKPAdelicCubeTorus K hζ) :
    (sourceKPAdelicTorusInducingCube K hζ b).val.val = b.val := rfl

theorem sourceKPAdelicTorusInducingCharacter_cube (s : ℂ) (b : sourceKPAdelicCubeTorus K hζ) :
    sourceKPAdelicTorusInducingCharacter K hζ s (sourceKPAdelicTorusInducingCube K hζ b) =
      sourceKPAdelicParametricCharacter K hζ s b :=
  sourceKPAdelicParametricRationalCharacter_fromCube K hζ s b

theorem sourceKPAdelicTorusInducingCube_commute (b : sourceKPAdelicCubeTorus K hζ)
    (g : sourceKPAdelicCoveringTorus K hζ) :
    Commute (sourceKPAdelicTorusInducingCube K hζ b).val g := by
  apply Subtype.ext
  change b.val * g.val = g.val * b.val
  obtain ⟨z, a, hg⟩ := (sourceKPAdelicCoveringTorus_mem_iff K hζ g.val).mp g.property
  rw [hg]
  exact ((sourceKPAdelicProjectiveCenter_commute K hζ z b.val).symm.mul_right
    (sourceKPAdelicCubeTorus_commute_diagonal K hζ b a)).eq

theorem sourceKPAdelicTorusInducedRepresentation_cube (s : ℂ) (b : sourceKPAdelicCubeTorus K hζ)
    (f : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicTorusInducingCube K hζ b).val f =
      (sourceKPAdelicParametricCharacter K hζ s b : ℂ) • f := by
  apply Subtype.ext
  funext g
  change f.val (g * (sourceKPAdelicTorusInducingCube K hζ b).val) =
    (sourceKPAdelicParametricCharacter K hζ s b : ℂ) * f.val g
  rw [← (sourceKPAdelicTorusInducingCube_commute K hζ b g).eq,
    sourceAlgebraicInducedSpace_covariant, sourceKPAdelicTorusInducingRepresentation_apply,
    sourceKPAdelicTorusInducingCharacter_cube]

def sourceKPAdelicTorusInducingCenter (z : rootsOfUnity 3 K) : sourceKPAdelicTorusInducingSubgroup K hζ :=
  sourceKPAdelicRationalCubeToInducing K hζ
    (sourceKPAdelicRationalCubeFromCube K hζ (sourceKPAdelicCubeTorusEquiv K hζ (z, 1)))

theorem sourceKPAdelicTorusInducingCenter_val (z : rootsOfUnity 3 K) :
    (sourceKPAdelicTorusInducingCenter K hζ z).val.val = sourceKPAdelicProjectiveCenter K hζ z := by
  change (sourceKPAdelicCubeTorusEquiv K hζ (z, 1)).val = _
  rw [sourceKPAdelicCubeTorusEquiv_val]
  change sourceKPAdelicProjectiveCenter K hζ z * sourceKPAdelicCubeLift K hζ 1 = _
  rw [map_one, mul_one]

theorem sourceKPAdelicTorusInducingCharacter_center (s : ℂ) (z : rootsOfUnity 3 K) :
    sourceKPAdelicTorusInducingCharacter K hζ s (sourceKPAdelicTorusInducingCenter K hζ z) =
      sourceKPAdelicCentralComplex K hζ z :=
  sourceKPAdelicParametricRationalCharacter_center K hζ s z

theorem sourceKPAdelicTorusInducedRepresentation_center (s : ℂ) (z : rootsOfUnity 3 K)
    (f : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicTorusInducingCenter K hζ z).val f =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) • f := by
  apply Subtype.ext
  funext g
  change f.val (g * (sourceKPAdelicTorusInducingCenter K hζ z).val) =
    (sourceKPAdelicCentralComplex K hζ z : ℂ) * f.val g
  have hc : g * (sourceKPAdelicTorusInducingCenter K hζ z).val =
      (sourceKPAdelicTorusInducingCenter K hζ z).val * g := by
    apply Subtype.ext
    change g.val * (sourceKPAdelicTorusInducingCenter K hζ z).val.val =
      (sourceKPAdelicTorusInducingCenter K hζ z).val.val * g.val
    rw [sourceKPAdelicTorusInducingCenter_val]
    exact (sourceKPAdelicProjectiveCenter_commute K hζ z g.val).eq.symm
  rw [hc, sourceAlgebraicInducedSpace_covariant,
    sourceKPAdelicTorusInducingRepresentation_apply, sourceKPAdelicTorusInducingCharacter_center]

theorem sourceKPAdelicTorusInducedRepresentation_center_injective (s : ℂ) :
    Function.Injective (fun z : rootsOfUnity 3 K => sourceKPAdelicTorusInducedRepresentation K hζ s
      (sourceKPAdelicTorusInducingCenter K hζ z).val) := by
  intro z w h
  have he := congrArg (fun A : Module.End ℂ (SourceKPAdelicTorusInducedSpace K hζ s) =>
    (A (sourceKPAdelicTorusInducedSection K hζ s)).val 1) h
  rw [sourceKPAdelicTorusInducedRepresentation_center,
    sourceKPAdelicTorusInducedRepresentation_center] at he
  change (sourceKPAdelicCentralComplex K hζ z : ℂ) *
      (sourceKPAdelicTorusInducedSection K hζ s).val 1 =
    (sourceKPAdelicCentralComplex K hζ w : ℂ) *
      (sourceKPAdelicTorusInducedSection K hζ s).val 1 at he
  simp only [sourceKPAdelicTorusInducedSection_one, mul_one] at he
  exact sourceKPAdelicCentralComplex_injective K hζ (Units.ext he)

theorem sourceKPAdelicTorusInducedSpace_rational (s : ℂ) (y : Kˣ)
    (f : SourceKPAdelicTorusInducedSpace K hζ s) (g : sourceKPAdelicCoveringTorus K hζ) :
    f.val ((sourceKPAdelicRationalCubeToInducing K hζ (sourceKPAdelicRationalCubeFromRational K hζ y)).val * g) =
      f.val g := by
  rw [sourceAlgebraicInducedSpace_covariant, sourceKPAdelicTorusInducingRepresentation_apply]
  change (sourceKPAdelicParametricRationalCharacter K hζ s (sourceKPAdelicRationalCubeFromRational K hζ y) : ℂ) *
    f.val g = f.val g
  rw [sourceKPAdelicParametricRationalCharacter_fromRational, Units.val_one, one_mul]

theorem sourceKPAdelicTorusInducingCharacter_sixth :
    sourceKPAdelicTorusInducingCharacter K hζ (1/6 : ℂ) =
      (sourceKPAdelicRationalCubeCharacter K hζ).comp (sourceKPAdelicTorusInducingToRationalCube K hζ) := by
  rw [sourceKPAdelicTorusInducingCharacter, sourceKPAdelicParametricRationalCharacter_sixth]

end
end ArtinMatthews
