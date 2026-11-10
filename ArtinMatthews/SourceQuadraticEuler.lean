module

public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.QuadraticKummerEuler
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourceQuadraticConductorProduct
public import ArtinMatthews.SourceQuadraticPrimitive
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source family's principal branch and its nonprincipal
two-factor Dedekind identity on the half-plane of absolute convergence. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

theorem sourceQuadraticGaloisCharacter_zero : sourceQuadraticGaloisCharacter F S₀ hζ 0 = 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  apply (quadraticKummerCharacter_one_iff (sourcePrimitiveRootSix F hζ)
    (sourcePrimeExponentUnit F hζ S₀ 0)).mpr
  refine ⟨1, ?_⟩
  rw [sourcePrimeExponentUnit_zero, Units.val_one, one_pow]

theorem sourceQuadraticConductor_zero : sourceQuadraticConductor F S₀ hζ 0 = 1 := by
  rw [sourceQuadraticConductor_eq_exterior_of_localSquares F S₀ hζ 0
    (by intro P; simp) (by
      intro P _
      refine ⟨1, ?_⟩
      rw [sourcePrimeExponentUnit_zero, Units.val_one, map_one, one_pow])]
  simp [sourcePrimeExponentIdeal]

variable [IsTotallyComplex F]

theorem sourceQuadraticRayCharacter_zero_idealHom (I : FractionalIdealGroup F) :
    (sourceQuadraticRayCharacter F S₀ hζ 0).idealHom I = 1 := by
  rw [sourceQuadraticRayCharacter_idealHom, sourceQuadraticGaloisCharacter_zero]
  change (∏ᶠ P : HeightOneSpectrum (𝓞 F),
    (1 : ℂˣ) ^ FractionalIdeal.count F P I.val) = 1
  simp only [one_zpow, finprod_one]

theorem sourceQuadraticRayCharacter_zero_coefficient (J : integralFractionalIdeals F) :
    (sourceQuadraticRayCharacter F S₀ hζ 0).coefficient J = 1 := by
  have hc : IsCoprime (EvenRayCharacter.underlyingIdeal J)
      (sourceQuadraticConductor F S₀ hζ 0) := by
    rw [sourceQuadraticConductor_zero]
    exact isCoprime_one_right
  simp only [EvenIdealRayCharacter.coefficient, ite_eq_left hc,
    sourceQuadraticRayCharacter_zero_idealHom, Units.val_one]

theorem sourceQuadraticRayCharacter_zero_dirichlet {s : ℂ} (hs : 1 < s.re) :
    (sourceQuadraticRayCharacter F S₀ hζ 0).dirichlet s = dedekindZeta F s := by
  rw [← integralDedekindDirichlet_eq_dedekindZeta F hs]
  unfold EvenIdealRayCharacter.dirichlet integralDedekindDirichlet
  simp only [sourceQuadraticRayCharacter_zero_coefficient, one_mul]

theorem sourceQuadraticRayCharacter_dedekind_factor (e : E) (he : ∀ P, e P ≤ 1) (hne : e ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (SourceQuadraticField F S₀ hζ e) s =
      dedekindZeta F s * (sourceQuadraticRayCharacter F S₀ hζ e).dirichlet s := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  exact ArtinRay.quadraticNormConductor_dedekind_factor
    (sourceQuadraticField_finrank_two F S₀ hζ e he hne)
    (sourceQuadraticGaloisCharacter F S₀ hζ e) (quadraticKummerCharacter_injective _ _) hs

end
end ArtinMatthews.SourceEulerAssembly
