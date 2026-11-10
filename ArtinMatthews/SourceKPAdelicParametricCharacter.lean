module

public import ArtinMatthews.SourceKPIdeleComplexNorm
public import ArtinMatthews.SourceKPAdelicWeylCharacter
public import ArtinMatthews.SourceKPAdelicExceptionalLocalNorm
public import ArtinMatthews.SourceKPAdelicExceptionalRational
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

/-! The actual complex-parameter genuine character of the central cube torus. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicParametricCharacterPair (s : ℂ) :
    rootsOfUnity 3 K × SourceKPIdeleCubes K →* ℂˣ where
  toFun p := sourceKPAdelicCentralComplex K hζ p.1 * sourceKPIdeleComplexNorm K s p.2.val
  map_one' := by
    change sourceKPAdelicCentralComplex K hζ 1 * sourceKPIdeleComplexNorm K s 1 = 1
    rw [map_one, map_one, mul_one]
  map_mul' x y := by
    change sourceKPAdelicCentralComplex K hζ (x.1*y.1) *
      sourceKPIdeleComplexNorm K s (x.2.val*y.2.val) = _
    rw [map_mul, map_mul]
    ac_rfl

def sourceKPAdelicParametricCharacter (s : ℂ) : sourceKPAdelicCubeTorus K hζ →* ℂˣ :=
  (sourceKPAdelicParametricCharacterPair K hζ s).comp
    (sourceKPAdelicCubeTorusEquiv K hζ).symm.toMonoidHom

theorem sourceKPAdelicParametricCharacter_equiv (s : ℂ)
    (p : rootsOfUnity 3 K × SourceKPIdeleCubes K) :
    sourceKPAdelicParametricCharacter K hζ s (sourceKPAdelicCubeTorusEquiv K hζ p) =
      sourceKPAdelicCentralComplex K hζ p.1 * sourceKPIdeleComplexNorm K s p.2.val := by
  let E := sourceKPAdelicCubeTorusEquiv K hζ
  change sourceKPAdelicParametricCharacterPair K hζ s (E.symm (E p)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem sourceKPAdelicParametricCharacter_center (s : ℂ) (z : rootsOfUnity 3 K) :
    sourceKPAdelicParametricCharacter K hζ s (sourceKPAdelicCubeTorusEquiv K hζ (z, 1)) =
      sourceKPAdelicCentralComplex K hζ z := by
  rw [sourceKPAdelicParametricCharacter_equiv]
  change sourceKPAdelicCentralComplex K hζ z * sourceKPIdeleComplexNorm K s 1 = _
  rw [map_one, mul_one]

theorem sourceKPAdelicParametricCharacter_center_injective (s : ℂ) :
    Function.Injective (fun z : rootsOfUnity 3 K =>
      sourceKPAdelicParametricCharacter K hζ s (sourceKPAdelicCubeTorusEquiv K hζ (z, 1))) := by
  intro z w h
  simp only [sourceKPAdelicParametricCharacter_center] at h
  exact sourceKPAdelicCentralComplex_injective K hζ h

theorem sourceKPAdelicParametricCharacter_cube (s : ℂ) (z : rootsOfUnity 3 K)
    (x : IdeleGroup (𝓞 K) K) :
    ((sourceKPAdelicParametricCharacter K hζ s
      (sourceKPAdelicCubeTorusEquiv K hζ (z, sourceKPIdeleCube K x)) : ℂˣ) : ℂ) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        Complex.exp ((3*s) * (Real.log (sourceKPIdeleAbsoluteNorm K x) : ℂ)) := by
  rw [sourceKPAdelicParametricCharacter_equiv, Units.val_mul]
  change (sourceKPAdelicCentralComplex K hζ z : ℂ) *
    ((sourceKPIdeleComplexNorm K s (x^3) : ℂˣ) : ℂ) = _
  rw [sourceKPIdeleComplexNorm_cube]

theorem sourceKPAdelicParametricCharacter_cube_ofAdicCompletion (s : ℂ)
    (P : HeightOneSpectrum (𝓞 K)) (z : rootsOfUnity 3 K) (u : (P.adicCompletion K)ˣ) :
    ((sourceKPAdelicParametricCharacter K hζ s
      (sourceKPAdelicCubeTorusEquiv K hζ
        (z, sourceKPIdeleCube K (IdeleGroup.ofAdicCompletion (𝓞 K) K P u))) : ℂˣ) : ℂ) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        Complex.exp ((3*s) * (Real.log ‖(u : P.adicCompletion K)‖ : ℂ)) := by
  rw [sourceKPAdelicParametricCharacter_cube, sourceKPIdeleAbsoluteNorm_ofAdicCompletion]

theorem sourceKPAdelicParametricCharacter_sixth :
    sourceKPAdelicParametricCharacter K hζ (1/6 : ℂ) = sourceKPAdelicExceptionalCharacter K hζ := by
  apply MonoidHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (sourceKPAdelicCubeTorusEquiv K hζ).surjective x
  rw [sourceKPAdelicParametricCharacter_equiv, sourceKPAdelicExceptionalCharacter_equiv,
    sourceKPIdeleComplexNorm_sixth]

theorem sourceKPAdelicParametricCharacter_weyl (s : ℂ) :
    sourceKPAdelicParametricCharacter K hζ (-s) =
      (sourceKPAdelicParametricCharacter K hζ s).comp
        (sourceKPAdelicCubeTorusWeyl K hζ).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (sourceKPAdelicCubeTorusEquiv K hζ).surjective x
  change sourceKPAdelicParametricCharacter K hζ (-s) (sourceKPAdelicCubeTorusEquiv K hζ p) =
    sourceKPAdelicParametricCharacter K hζ s
      (sourceKPAdelicCubeTorusWeyl K hζ (sourceKPAdelicCubeTorusEquiv K hζ p))
  rw [sourceKPAdelicCubeTorusWeyl_equiv,
    sourceKPAdelicParametricCharacter_equiv, sourceKPAdelicParametricCharacter_equiv,
    sourceKPIdeleComplexNorm_neg]
  change sourceKPAdelicCentralComplex K hζ p.1 * (sourceKPIdeleComplexNorm K s p.2.val)⁻¹ =
    sourceKPAdelicCentralComplex K hζ p.1 * sourceKPIdeleComplexNorm K s p.2.val⁻¹
  rw [map_inv]

theorem sourceKPAdelicParametricCharacter_negative_sixth :
    sourceKPAdelicParametricCharacter K hζ (-1/6 : ℂ) = sourceKPAdelicWeylExceptionalCharacter K hζ := by
  simpa only [neg_div, sourceKPAdelicParametricCharacter_sixth,
    sourceKPAdelicWeylExceptionalCharacter] using
    sourceKPAdelicParametricCharacter_weyl K hζ (1/6 : ℂ)

theorem sourceKPAdelicParametricCharacter_rational (s : ℂ) (g : PGL(2, K))
    (x : sourceKPAdelicCubeTorus K hζ)
    (hx : sourceKPAdelicProjectiveRationalLift K hζ g = x.val) :
    sourceKPAdelicParametricCharacter K hζ s x = 1 := by
  obtain ⟨y, _, hz, hy⟩ := sourceKPAdelicExceptionalCharacter_rational_coordinates K hζ g x hx
  let E := sourceKPAdelicCubeTorusEquiv K hζ
  let p := E.symm x
  have hp : E p = x := E.apply_symm_apply x
  rw [← hp, sourceKPAdelicParametricCharacter_equiv]
  change p.1 = 1 at hz
  change p.2.val = IdeleGroup.unitEmbedding (𝓞 K) K y at hy
  rw [hz, map_one, one_mul, hy, sourceKPIdeleComplexNorm_principal]

end
end ArtinMatthews
