module

public import ArtinMatthews.VaryingKummerAnalyticRayPrimitivePrincipal
public import OAI.NumberTheory.DirichletL.FiniteFourier
public import ArtinMatthews.VaryingKummerAnalyticRayConductorCharacter
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

/-! A genuinely constructed primitive ideal-conductor presentation of the
original ray character, including its actual ideal ray-class character and
its integral principal law at the smaller conductor. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

theorem exists_primitive_idealRay_presentation :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
      (hMf : rationalModulusIdeal (𝓞 K) N ≤ f)
      (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
      (χ : IdealRayClassGroup (integralIdealRayModulus f hf) →* ℂˣ),
      IsPrimitiveOnIdeals φ ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) N).absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
        if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
          then φ (Ideal.Quotient.mk f a) else 0) ∧
      (∀ u : (𝓞 K)ˣ, φ (Ideal.Quotient.mk f (u:𝓞 K)) = 1) ∧
      (∃ e : ℕ, 0 < e ∧ ∀ c, χ c ^ e = 1) ∧
      (∀ c, χ (conductorIdealProjection f hf hMf c) = ψ.rayClassCharacter c) ∧
      ∀ (a : 𝓞 K) (ha : a ≠ 0) (hac : IsCoprime (Ideal.span {a}) f),
        (χ (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus f hf))
          (integralPrincipalPrimeToIdeal f hf a ha hac)) : ℂ) = φ (Ideal.Quotient.mk f a) := by
  obtain ⟨f,φ,hMf,hf,hprim,hnorm,hmask,_hfactor,hunit⟩ :=
    ψ.exists_primitive_residue_conductor
  exact ⟨f,hf,hMf,φ,ψ.descendedIdealRayCharacter f hf hMf φ hmask,
    hprim,hnorm,hmask,hunit,
    ψ.descendedIdealRayCharacter_finiteOrder f hf hMf φ hmask,
    ψ.descendedIdealRayCharacter_projection f hf hMf φ hmask,
    ψ.descendedIdealRayCharacter_principal f hf hMf φ hmask⟩

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
