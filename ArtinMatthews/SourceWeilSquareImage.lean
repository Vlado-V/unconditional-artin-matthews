module

public import ArtinMatthews.AllowedGeneratorBase
public import ArtinMatthews.PowerClassSixthCRT
public import ArtinMatthews.StandardWeilHilbertProducts
public import ArtinMatthews.SLocalHilbertExponent
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual paper B6 is sent to square classes by the genuine quotient
map. Its square-class image is isotropic for the actual quadratic Hilbert
form; no independently chosen B2 is identified with B6. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open QuadraticWeil
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

def sourceRingSquareMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SLocalRingPowerClasses K 6 S →* SLocalPowerClasses K 2 S :=
  (MonoidHom.fst (SLocalPowerClasses K 2 S) (SLocalPowerClasses K 3 S)).comp
    ((sLocalSixthCRT K S).toMonoidHom.comp
      ((sLocalRingPowerEquiv K 6 S).trans (sWholePowerEquiv K 6 S)).toMonoidHom)

@[simp] theorem sourceRingSquareMap_global
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    sourceRingSquareMap K S (sLocalRingGlobalClassMap K 6 S a) =
      sLocalGlobalClassMap K 2 S a := by
  change (sLocalSixthCRT K S (sWholePowerEquiv K 6 S
    (sLocalRingPowerEquiv K 6 S (sLocalRingGlobalClassMap K 6 S a)))).1 = _
  rw [sLocalRingPowerEquiv_globalClass, sWholePowerEquiv_globalClass,
    sLocalSixthCRT_globalClass]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem chosenB_squareImage_isotropic
    (a : SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀)) (ha : a ∈ AllowedGenerators.chosenB K hζ S₀)
    (b : SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀)) (hb : b ∈ AllowedGenerators.chosenB K hζ S₀) :
    sLocalHilbertForm K 2 (numberFieldQuadraticRoots K) (sourceHilbertSet K S₀)
      (sourceRingSquareMap K (sourceHilbertSet K S₀) a)
      (sourceRingSquareMap K (sourceHilbertSet K S₀) b) = 1 := by
  let e := (sLocalRingPowerEquiv K 6 (sourceHilbertSet K S₀)).trans
    (sWholePowerEquiv K 6 (sourceHilbertSet K S₀))
  have h6 := AllowedGenerators.chosenB_isotropic K hζ S₀ b hb a ha
  change sLocalHilbertForm K 6
    (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ))
    (sourceHilbertSet K S₀) (e a) (e b) = 1 at h6
  have he := sLocalHilbertForm_sixth_square K (numberFieldQuadraticRoots K)
    (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ))
    (sourceHilbertSet K S₀) (e a) (e b)
  apply Subtype.ext
  exact he.trans ((congrArg (fun z : rootsOfUnity 6 K => (z : Kˣ) ^ 3) h6).trans (one_pow 3))

def chosenB_squareImage : Subgroup (SLocalPowerClasses K 2 (sourceHilbertSet K S₀)) :=
  (AllowedGenerators.chosenB K hζ S₀).map (sourceRingSquareMap K (sourceHilbertSet K S₀))

theorem chosenB_squareImage_isotropic_all :
    ∀ x ∈ chosenB_squareImage K hζ S₀, ∀ y ∈ chosenB_squareImage K hζ S₀,
      sLocalHilbertForm K 2 (numberFieldQuadraticRoots K) (sourceHilbertSet K S₀) x y = 1 := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  exact chosenB_squareImage_isotropic K hζ S₀ a ha b hb

def chosenB_squareImageHom :
    AllowedGenerators.chosenB K hζ S₀ →* chosenB_squareImage K hζ S₀ :=
  ((sourceRingSquareMap K (sourceHilbertSet K S₀)).comp
    (AllowedGenerators.chosenB K hζ S₀).subtype).codRestrict _
      (fun b => ⟨b.val, b.property, rfl⟩)

end
end ArtinMatthews
