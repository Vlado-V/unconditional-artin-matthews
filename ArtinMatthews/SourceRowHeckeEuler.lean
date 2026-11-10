module

public import ArtinMatthews.SourceRowKummerRay
public import ArtinMatthews.PrincipalAngularGaussian
public import ArtinMatthews.PrincipalAngularResidue
public import ArtinMatthews.SourceGlobalCorrection
public import ArtinMatthews.SourceGlobalEulerCoefficients
public import ArtinMatthews.SourceExteriorDirichletIdentification
public import ArtinMatthews.SourceGlobalEulerExtraction
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

/-! The source Euler quotient with actual Kummer and twisted ray series,
not just the product of unnamed prime values. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M) (hM : M ≠ ⊥)
variable (u : sourceRing F S₀) (hu : u ≠ 0)
local notation "S" => sourceHilbertSet F S₀

include hS in
theorem sourceGlobalCalF_eq_Hecke (hcut : probePrimeCutoff F ⊆ S)
    (ξ w z : ℂ) (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    sourceGlobalCalF F hζ S₀ hS η u ξ w z =
      principalExteriorZeta S (6 * z) *
      principalAngularExteriorL (sourceRowKummerRay F hζ S₀ u hu) S w /
      principalAngularExteriorL (sourceRowKummerTwist F hζ S₀ u hu η hM) S ξ *
      sourceGlobalCorrection F hζ S₀ η u hu (ξ, w, z) := by
  have hA : sourcePrimeRowCharacter F hζ S₀ u hu = fun P =>
      (sourceRowKummerRay F hζ S₀ u hu).allCoefficient P.val.asIdeal :=
    funext (fun P => (sourceRowKummerRay_prime F hζ S₀ u hu P).symm)
  have hB : sourcePrimeRowTwist F hζ S₀ u hu η = fun P =>
      (sourceRowKummerTwist F hζ S₀ u hu η hM).allCoefficient P.val.asIdeal :=
    funext (fun P => (sourceRowKummerTwist_prime F hζ S₀ u hu η hM P).symm)
  have hz₁ : 1 < (6 * z).re := by
    have he : ((6 : ℂ) * z).re = 6 * z.re := by norm_num [Complex.mul_re]
    rw [he]
    linarith
  rw [sourceGlobalCalF_eq_normalized F hζ S₀ hS η u hu ξ w z hcut hξ hw hz, hA, hB,
    sourceExteriorValueEuler_eq_exteriorZeta F S₀ (6 * z) hz₁,
    sourceExteriorValueEuler_eq_angularL F S₀ _ w (by linarith),
    sourceExteriorValueEuler_eq_angularL F S₀ _ ξ (by linarith)]

end
end ArtinMatthews.SourceEulerAssembly
