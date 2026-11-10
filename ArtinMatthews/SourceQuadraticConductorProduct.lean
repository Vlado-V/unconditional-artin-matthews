module

public import ArtinMatthews.SourceQuadraticConductorFactorization
public import ArtinMatthews.SourceQuadraticLocalClasses
public import ArtinMatthews.QuadraticKummerLocalConductor
public import ArtinMatthews.SourcePrimeExponentProducts
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

/-! Equal actual S-local square classes remove every S conductor
factor from the product radicand. For disjoint squarefree supports,
the resulting primitive conductor is exactly the product ideal. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open AngularLambda
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "S" => sourceHilbertSet F S₀

theorem sourceQuadraticConductor_wild_zero_of_localSquares (e : E)
    (hsquare : ∀ P : HeightOneSpectrum (𝓞 F), P ∈ S →
      ∃ s : P.adicCompletion F,
        s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ e : F)) :
    sourceQuadraticWildExponents F S₀ hζ e = 0 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  ext P
  rw [sourceQuadraticWildExponents, Finsupp.filter_apply, Finsupp.zero_apply]
  by_cases hP : P ∈ S
  · rw [ite_eq_left hP]
    change integralIdealFiniteModulus
      (ArtinRay.abelianNormConductorIdeal F (SourceQuadraticField F S₀ hζ e))
      (ArtinRay.abelianNormConductorIdeal_ne_bot F _) P = 0
    rw [ArtinRay.abelianNormConductorIdeal_modulus]
    exact quadraticKummer_conductorExponent_eq_zero_of_localSquare
      (sourcePrimitiveRootSix F hζ) (sourcePrimeExponentUnit F hζ S₀ e) P (hsquare P hP)
  · exact ite_eq_right hP

theorem sourceQuadraticConductor_eq_exterior_of_localSquares (e : E) (he : ∀ P, e P ≤ 1)
    (hsquare : ∀ P : HeightOneSpectrum (𝓞 F), P ∈ S →
      ∃ s : P.adicCompletion F,
        s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ e : F)) :
    sourceQuadraticConductor F S₀ hζ e = sourcePrimeExponentIdeal F S₀ e := by
  rw [sourceQuadraticConductor_factorization F S₀ hζ e he, sourceQuadraticWildIdeal,
    sourceQuadraticConductor_wild_zero_of_localSquares F S₀ hζ e hsquare]
  simp [sourceFullExponentIdeal, Finsupp.prod]

theorem sourceQuadraticDisjoint_add_squarefree (e f : E) (he : ∀ P, e P ≤ 1)
    (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support) :
    ∀ P, (e + f) P ≤ 1 := by
  intro P
  rw [Finsupp.add_apply]
  by_cases hP : e P = 0
  · simpa only [hP, zero_add] using hf P
  · have hfP : f P = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun hm => Finset.disjoint_left.mp hd (Finsupp.mem_support_iff.mpr hP) hm
    simpa only [hfP, add_zero] using he P

theorem sourceQuadraticConductor_eq_product_of_class_eq (e f : E)
    (he : ∀ P, e P ≤ 1) (hf : ∀ P, f P ≤ 1) (hd : Disjoint e.support f.support)
    (hclass : sourceQuadraticLocalClass F S₀ hζ e = sourceQuadraticLocalClass F S₀ hζ f) :
    sourceQuadraticConductor F S₀ hζ (e + f) =
      sourcePrimeExponentIdeal F S₀ e * sourcePrimeExponentIdeal F S₀ f := by
  rw [sourceQuadraticConductor_eq_exterior_of_localSquares F S₀ hζ (e + f)
    (sourceQuadraticDisjoint_add_squarefree F S₀ e f he hf hd)
    (sourceQuadraticLocalClass_eq_localSquare F S₀ hζ e f hclass),
    sourcePrimeExponentIdeal_add]

end
end ArtinMatthews.SourceEulerAssembly
