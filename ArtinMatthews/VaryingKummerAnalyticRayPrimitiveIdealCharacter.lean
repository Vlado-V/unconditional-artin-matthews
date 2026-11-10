module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealCharacter
public import OAI.NumberTheory.DirichletL.FiniteFourier
public import ArtinMatthews.VaryingKummerAnalyticRayPrimitivePresentation
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

/-! The original character produces genuine primitive ideal-modulus ray
data on the full fractional-ideal group. All old prime-to ideal values
are preserved by the constructed extension. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

theorem exists_primitive_idealCharacter :
    ∃ (f : Ideal (𝓞 K)) (_hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (Ψ : EvenIdealRayCharacter K f),
      IsPrimitiveOnIdeals Ψ.residue ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) N).absNorm ∧
      (∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
        if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
          then Ψ.residue (Ideal.Quotient.mk f a) else 0) ∧
      ∀ I : primeToModulusIdeals (rationalIdealRayModulus K N),
        Ψ.idealHom (I:FractionalIdealGroup K) = ψ.idealHom (I:FractionalIdealGroup K) := by
  obtain ⟨f,hf,hMf,φ,χ,hprim,hnorm,hmask,_hunit,hfinite,hagree,hprincipal⟩ :=
    ψ.exists_primitive_idealRay_presentation
  let Ψ := EvenIdealRayCharacter.ofIdealRayClass hf χ hfinite φ hprincipal
  refine ⟨f,hf,hMf,Ψ,hprim,hnorm,hmask,?_⟩
  intro I
  let hnm := integralIdealRayModulus_antitone (rationalModulusIdeal_ne_bot N) hf hMf
  have H := EvenIdealRayCharacter.ofIdealRayClass_idealHom_primeTo hf χ hfinite φ hprincipal
    (primeToIdealConductorInclusion hnm I)
  change Ψ.idealHom (I:FractionalIdealGroup K) = _ at H
  rw [← idealConductorProjection_ideal hnm I] at H
  exact H.trans ((hagree _).trans (ψ.rayClassCharacter_ideal I))

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
