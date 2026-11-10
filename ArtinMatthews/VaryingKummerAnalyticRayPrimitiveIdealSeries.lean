module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import OAI.NumberTheory.DirichletL.FiniteFourier
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveIdealCharacter
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

/-! Exact primitive ideal-conductor coefficients of the original series.
The old bad-prime mask is retained literally, including every prime removed
by the original rational modulus but absent from the primitive conductor. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

theorem coefficient_eq_primitive_mask (f : Ideal (𝓞 K))
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f)
    (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus K N),
      Ψ.idealHom (I:FractionalIdealGroup K) = ψ.idealHom (I:FractionalIdealGroup K))
    (J : integralFractionalIdeals K) :
    ψ.coefficient J = if IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
      then Ψ.coefficient J else 0 := by
  by_cases hcop : IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
  · have hcopf : IsCoprime (underlyingIdeal J) f :=
      hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hMf)
    have H := hagree (integralIdealPrimeToIdeal (rationalModulusIdeal (𝓞 K) N)
      (rationalModulusIdeal_ne_bot N) (underlyingIdeal J) (underlyingIdeal_ne_bot J) hcop)
    change Ψ.idealHom (integralIdealFractionalUnit (underlyingIdeal J) (underlyingIdeal_ne_bot J)) =
      ψ.idealHom (integralIdealFractionalUnit (underlyingIdeal J) (underlyingIdeal_ne_bot J)) at H
    rw [underlyingIdeal_unit] at H
    simp only [coefficient,EvenIdealRayCharacter.coefficient,ite_eq_left hcop,ite_eq_left hcopf]
    exact congrArg Units.val H.symm
  · simp only [coefficient,ite_eq_right hcop]

theorem dirichlet_eq_primitive_masked_series (f : Ideal (𝓞 K))
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f)
    (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus K N),
      Ψ.idealHom (I:FractionalIdealGroup K) = ψ.idealHom (I:FractionalIdealGroup K)) (s : ℂ) :
    ψ.dirichlet s = ∑' J : integralFractionalIdeals K,
      (if IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
        then Ψ.coefficient J else 0) * ((FractionalIdeal.absNorm J.val.val : ℝ):ℂ)^(-s) := by
  apply tsum_congr
  intro J
  rw [ψ.coefficient_eq_primitive_mask f hMf Ψ hagree J]

theorem exists_primitive_idealSeries :
    ∃ (f : Ideal (𝓞 K)) (_hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f),
      IsPrimitiveOnIdeals Ψ.residue ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) N).absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
        if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
          then Ψ.residue (Ideal.Quotient.mk f a) else 0) ∧
      (∀ J : integralFractionalIdeals K,
        ψ.coefficient J = if IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
          then Ψ.coefficient J else 0) ∧
      ∀ s : ℂ, ψ.dirichlet s = ∑' J : integralFractionalIdeals K,
        (if IsCoprime (underlyingIdeal J) (rationalModulusIdeal (𝓞 K) N)
          then Ψ.coefficient J else 0) * ((FractionalIdeal.absNorm J.val.val : ℝ):ℂ)^(-s) := by
  obtain ⟨f,hf,hMf,Ψ,hprim,hnorm,hmask,hagree⟩ := ψ.exists_primitive_idealCharacter
  exact ⟨f,hf,hMf,Ψ,hprim,hnorm,hmask,
    ψ.coefficient_eq_primitive_mask f hMf Ψ hagree,
    ψ.dirichlet_eq_primitive_masked_series f hMf Ψ hagree⟩

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
