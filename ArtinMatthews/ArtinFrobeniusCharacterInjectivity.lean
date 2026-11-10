module

public import ArtinMatthews.ArtinRaySmallModulus
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import ArtinMatthews.VaryingKummerAnalyticRayCharacterMultiplicityCount
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

/-! Faithfulness of the actual finite abelian Frobenius family on coprime
ideal coefficients. The proof uses the genuine Artin-map nonprincipality
theorem and introduces no prime-distribution or zero-exclusion input. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section

namespace GaloisIdealCharacter
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem idealHom_div (χ θ : Gal(L/K) →* ℂˣ) (I : FractionalIdealGroup K) :
    idealHom K L (χ/θ) I = idealHom K L χ I / idealHom K L θ I := by
  unfold idealHom
  simp only [MonoidHom.div_apply,div_zpow]
  exact finprod_div_distrib (finite_factor_support K L χ I) (finite_factor_support K L θ I)

end GaloisIdealCharacter

namespace ArtinRay
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]

theorem discriminantDegreeRayCharacter_coefficient_injective :
    Function.Injective (fun χ : Gal(L/K) →* ℂˣ =>
      (discriminantDegreeRayCharacter (K := K) (L := L) χ).coefficient) := by
  intro χ θ hcoeff
  by_contra hne
  have hdiv : χ/θ ≠ 1 := fun h => hne (div_eq_one.mp h)
  obtain ⟨I,hI,hcop,hvalue⟩ := discriminantDegreeRayCharacter_isNonprincipal (χ/θ) hdiv
  apply hvalue
  have he := (EvenRayCharacter.agreesOnCoprimeIdeals_iff_coefficient_eq
    (discriminantDegreeRayCharacter (K := K) (L := L) χ)
    (discriminantDegreeRayCharacter (K := K) (L := L) θ)).mpr hcoeff I hI hcop
  rw [discriminantDegreeRayCharacter_idealHom,discriminantDegreeRayCharacter_idealHom] at he
  rw [discriminantDegreeRayCharacter_idealHom,GaloisIdealCharacter.idealHom_div,he]
  simp

end ArtinRay
end
end ArtinMatthews.VaryingKummerAnalytic
