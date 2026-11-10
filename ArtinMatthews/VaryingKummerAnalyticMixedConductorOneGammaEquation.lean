module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual conductor-one completed equation in the positive half-plane
and the critical strip, with the shared normalization cancelled explicitly. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hMtop : M = ⊤) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hψ : ψ.IsNonprincipal)
include hψ hMtop

theorem conductorOneCompleted_eq_primitiveContinued_of_pos {s : ℂ} (hs : 0 < s.re) :
    ψ.conductorOneCompleted hMtop s = (mixedDiscriminantScale K : ℂ)^s *
      (mixedXiNormalization K : ℂ) * mixedGammaFactor K s *
        ψ.primitiveContinued hM hprim s := by
  have hC : (mixedXiNormalization K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'
  have hG := mixedGammaFactor_ne_zero K hs
  rw [ψ.primitiveContinued_eq_conductorOneCompletion hMtop hM hprim hψ]
  unfold conductorOneCompleted mixedCompletedIdealClass mixedInverseGammaFactor
  field_simp

/-- Literal Gamma-times-L functional equation on the critical strip for
the primitive character whose actual conductor is the unit ideal. -/
theorem conductorOne_gamma_functional_equation {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (mixedDiscriminantScale K : ℂ)^s * mixedGammaFactor K s *
        ψ.primitiveContinued hM hprim s =
      mixedClassRootNumber K (ψ.conductorOneClassCharacter hMtop) *
        (mixedDiscriminantScale K : ℂ)^(1-s) * mixedGammaFactor K (1-s) *
          ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) (1-s) := by
  have hr : 0 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have H := ψ.conductorOneCompleted_functional_equation hMtop hψ s
  rw [ψ.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM hprim hψ hs0,
    ψ.inverse.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hψ) hr] at H
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne')
  calc
    (mixedXiNormalization K : ℂ) * _ =
      (mixedDiscriminantScale K : ℂ)^s * (mixedXiNormalization K : ℂ) *
        mixedGammaFactor K s * ψ.primitiveContinued hM hprim s := by ring
    _ = _ := H
    _ = _ := by ring

/-- Reflection of genuine nontrivial zeros in the critical strip; no
functional-equation or zero-set hypothesis is supplied. -/
theorem conductorOne_primitive_zero_reflection {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ψ.primitiveContinued hM hprim s = 0 ↔
      ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) (1-s) = 0 := by
  have hr : 0 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hD : (mixedDiscriminantScale K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'
  have hW : mixedClassRootNumber K (ψ.conductorOneClassCharacter hMtop) ≠ 0 := by
    have H := ψ.conductorOneCompleted_rootNumber_norm hMtop
    intro hz
    rw [hz,norm_zero] at H
    exact zero_ne_one H
  have H := ψ.conductorOne_gamma_functional_equation hMtop hM hprim hψ hs0 hs1
  have hz := congrArg (fun z : ℂ => z = 0) H
  apply Eq.to_iff at hz
  simpa only [mul_eq_zero, Complex.cpow_ne_zero_iff.mpr (Or.inl hD), mixedGammaFactor_ne_zero K hs0,
    mixedGammaFactor_ne_zero K hr, hW, false_or] using hz

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
