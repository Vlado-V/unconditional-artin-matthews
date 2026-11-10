module

public import ArtinMatthews.SourceKPAdelicParametricCharacter
public import ArtinMatthews.SourceKPAdelicRationalCubeCharacter
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

/-! Descent of the actual parameter family to the rational-cube subgroup. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicParametricRationalPair (s : ℂ) :
    sourceKPAdelicCubeTorus K hζ × Kˣ →* ℂˣ :=
  (sourceKPAdelicParametricCharacter K hζ s).comp (MonoidHom.fst _ _)

theorem sourceKPAdelicParametricRationalPair_kernel (s : ℂ) :
    (sourceKPAdelicRationalCubeJoin K hζ).ker ≤ (sourceKPAdelicParametricRationalPair K hζ s).ker := by
  intro p hp
  let r := sourceKPAdelicRationalDiagonalLift K hζ
  change p.1.val * r p.2 = 1 at hp
  have he := congrArg (fun g : SourceKPAdelicProjective K hζ => g * (r p.2)⁻¹) hp
  rw [mul_inv_cancel_right, one_mul] at he
  have hr : r p.2⁻¹ = p.1.val := by rw [map_inv, he]
  change sourceKPAdelicParametricCharacter K hζ s p.1 = 1
  exact sourceKPAdelicParametricCharacter_rational K hζ s
    (sourceKPProjectiveDiagonalHom K p.2⁻¹) p.1 hr

def sourceKPAdelicParametricRationalCharacter (s : ℂ) : sourceKPAdelicRationalCubeTorus K hζ →* ℂˣ :=
  (QuotientGroup.lift (sourceKPAdelicRationalCubeJoin K hζ).ker
    (sourceKPAdelicParametricRationalPair K hζ s) (sourceKPAdelicParametricRationalPair_kernel K hζ s)).comp
      (QuotientGroup.quotientKerEquivRange (sourceKPAdelicRationalCubeJoin K hζ)).symm.toMonoidHom

theorem sourceKPAdelicParametricRationalCharacter_join (s : ℂ)
    (p : sourceKPAdelicCubeTorus K hζ × Kˣ) :
    sourceKPAdelicParametricRationalCharacter K hζ s
      ⟨sourceKPAdelicRationalCubeJoin K hζ p, ⟨p, rfl⟩⟩ =
      sourceKPAdelicParametricCharacter K hζ s p.1 := by
  let m := sourceKPAdelicRationalCubeJoin K hζ
  let e := QuotientGroup.quotientKerEquivRange m
  have he : e (QuotientGroup.mk' m.ker p) = ⟨m p, ⟨p, rfl⟩⟩ := rfl
  change (QuotientGroup.lift m.ker (sourceKPAdelicParametricRationalPair K hζ s)
    (sourceKPAdelicParametricRationalPair_kernel K hζ s))
      (e.symm (⟨m p, ⟨p, rfl⟩⟩ : m.range)) = _
  rw [← he, MulEquiv.symm_apply_apply]
  rfl

def sourceKPAdelicRationalCubeFromCube :
    sourceKPAdelicCubeTorus K hζ →* sourceKPAdelicRationalCubeTorus K hζ where
  toFun b := ⟨b.val, ⟨(b, 1), by
    change b.val * sourceKPAdelicRationalDiagonalLift K hζ 1 = b.val
    rw [map_one, mul_one]⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

def sourceKPAdelicRationalCubeFromRational : Kˣ →* sourceKPAdelicRationalCubeTorus K hζ where
  toFun y := ⟨sourceKPAdelicRationalDiagonalLift K hζ y, ⟨(1, y), by
    change 1 * sourceKPAdelicRationalDiagonalLift K hζ y = _
    rw [one_mul]⟩⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _

theorem sourceKPAdelicParametricRationalCharacter_fromCube (s : ℂ)
    (b : sourceKPAdelicCubeTorus K hζ) :
    sourceKPAdelicParametricRationalCharacter K hζ s (sourceKPAdelicRationalCubeFromCube K hζ b) =
      sourceKPAdelicParametricCharacter K hζ s b := by
  have he : sourceKPAdelicRationalCubeFromCube K hζ b =
      ⟨sourceKPAdelicRationalCubeJoin K hζ (b, 1), ⟨(b, 1), rfl⟩⟩ := by
    apply Subtype.ext
    change b.val = b.val * sourceKPAdelicRationalDiagonalLift K hζ 1
    rw [map_one, mul_one]
  rw [he, sourceKPAdelicParametricRationalCharacter_join]

theorem sourceKPAdelicParametricRationalCharacter_fromRational (s : ℂ) (y : Kˣ) :
    sourceKPAdelicParametricRationalCharacter K hζ s (sourceKPAdelicRationalCubeFromRational K hζ y) = 1 := by
  have he : sourceKPAdelicRationalCubeFromRational K hζ y =
      ⟨sourceKPAdelicRationalCubeJoin K hζ (1, y), ⟨(1, y), rfl⟩⟩ := by
    apply Subtype.ext
    change sourceKPAdelicRationalDiagonalLift K hζ y = 1 * sourceKPAdelicRationalDiagonalLift K hζ y
    rw [one_mul]
  rw [he, sourceKPAdelicParametricRationalCharacter_join, map_one]

theorem sourceKPAdelicParametricRationalCharacter_center (s : ℂ) (z : rootsOfUnity 3 K) :
    sourceKPAdelicParametricRationalCharacter K hζ s
      (sourceKPAdelicRationalCubeFromCube K hζ (sourceKPAdelicCubeTorusEquiv K hζ (z, 1))) =
      sourceKPAdelicCentralComplex K hζ z := by
  rw [sourceKPAdelicParametricRationalCharacter_fromCube, sourceKPAdelicParametricCharacter_center]

theorem sourceKPAdelicParametricRationalCharacter_sixth :
    sourceKPAdelicParametricRationalCharacter K hζ (1/6 : ℂ) = sourceKPAdelicRationalCubeCharacter K hζ := by
  apply MonoidHom.ext
  rintro ⟨x, hx⟩
  obtain ⟨p, rfl⟩ := hx
  rw [sourceKPAdelicParametricRationalCharacter_join, sourceKPAdelicRationalCubeCharacter_join,
    sourceKPAdelicParametricCharacter_sixth]

theorem sourceKPAdelicRationalCubeJoin_weyl (p : sourceKPAdelicCubeTorus K hζ × Kˣ) :
    sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicRationalCubeJoin K hζ p *
      (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ =
      sourceKPAdelicRationalCubeJoin K hζ (sourceKPAdelicCubeTorusWeyl K hζ p.1, p.2⁻¹) := by
  let W := sourceKPAdelicProjectiveWeyl K hζ
  let r := sourceKPAdelicRationalDiagonalLift K hζ
  have hr : W * r p.2 * W⁻¹ = r p.2⁻¹ := by
    change sourceKPAdelicProjectiveWeyl K hζ *
        sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K p.2) *
        (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ =
      sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K p.2⁻¹)
    rw [sourceKPAdelicProjectiveRationalLift_diagonal,
      sourceKPAdelicProjectiveRationalLift_diagonal,
      sourceKPAdelicProjectiveWeyl_conj_diagonal, map_inv]
  change W * (p.1.val * r p.2) * W⁻¹ =
    (sourceKPAdelicCubeTorusWeyl K hζ p.1).val * r p.2⁻¹
  rw [sourceKPAdelicCubeTorusWeyl_val]
  change W * (p.1.val * r p.2) * W⁻¹ = (W * p.1.val * W⁻¹) * r p.2⁻¹
  rw [← hr]
  group

def sourceKPAdelicRationalCubeWeyl :
    sourceKPAdelicRationalCubeTorus K hζ →* sourceKPAdelicRationalCubeTorus K hζ where
  toFun x := ⟨sourceKPAdelicProjectiveWeyl K hζ * x.val *
      (sourceKPAdelicProjectiveWeyl K hζ)⁻¹, by
    obtain ⟨p, hp⟩ := x.property
    refine ⟨(sourceKPAdelicCubeTorusWeyl K hζ p.1, p.2⁻¹), ?_⟩
    rw [← hp]
    exact (sourceKPAdelicRationalCubeJoin_weyl K hζ p).symm⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change sourceKPAdelicProjectiveWeyl K hζ * (x.val*y.val) *
      (sourceKPAdelicProjectiveWeyl K hζ)⁻¹ =
      (sourceKPAdelicProjectiveWeyl K hζ * x.val * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹) *
        (sourceKPAdelicProjectiveWeyl K hζ * y.val * (sourceKPAdelicProjectiveWeyl K hζ)⁻¹)
    group

theorem sourceKPAdelicRationalCubeWeyl_join (p : sourceKPAdelicCubeTorus K hζ × Kˣ) :
    sourceKPAdelicRationalCubeWeyl K hζ
      ⟨sourceKPAdelicRationalCubeJoin K hζ p, ⟨p, rfl⟩⟩ =
      ⟨sourceKPAdelicRationalCubeJoin K hζ (sourceKPAdelicCubeTorusWeyl K hζ p.1, p.2⁻¹),
        ⟨(sourceKPAdelicCubeTorusWeyl K hζ p.1, p.2⁻¹), rfl⟩⟩ := by
  apply Subtype.ext
  exact sourceKPAdelicRationalCubeJoin_weyl K hζ p

theorem sourceKPAdelicParametricRationalCharacter_weyl (s : ℂ) :
    sourceKPAdelicParametricRationalCharacter K hζ (-s) =
      (sourceKPAdelicParametricRationalCharacter K hζ s).comp (sourceKPAdelicRationalCubeWeyl K hζ) := by
  apply MonoidHom.ext
  rintro ⟨x, hx⟩
  obtain ⟨p, rfl⟩ := hx
  rw [MonoidHom.comp_apply, sourceKPAdelicRationalCubeWeyl_join,
    sourceKPAdelicParametricRationalCharacter_join, sourceKPAdelicParametricRationalCharacter_join]
  exact DFunLike.congr_fun (sourceKPAdelicParametricCharacter_weyl K hζ s) p.1

theorem sourceKPAdelicParametricRationalCharacter_negative_sixth :
    sourceKPAdelicParametricRationalCharacter K hζ (-1/6 : ℂ) =
      (sourceKPAdelicRationalCubeCharacter K hζ).comp (sourceKPAdelicRationalCubeWeyl K hζ) := by
  simpa only [neg_div, sourceKPAdelicParametricRationalCharacter_sixth] using
    sourceKPAdelicParametricRationalCharacter_weyl K hζ (1/6 : ℂ)

end
end ArtinMatthews
