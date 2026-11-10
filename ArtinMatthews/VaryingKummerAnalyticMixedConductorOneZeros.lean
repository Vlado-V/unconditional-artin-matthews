module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneGammaEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Nonvanishing in the convergent half-plane and the closed critical-strip
zero bound for the actual conductor-one completion. The left half-plane uses
the genuine inverse-character functional equation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hMtop : M = ⊤) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hM hprim hnp

theorem conductorOneCompleted_zero_iff_primitive {s : ℂ} (hs : 0 < s.re) :
    ψ.conductorOneCompleted hMtop s = 0 ↔ ψ.primitiveContinued hM hprim s = 0 := by
  rw [ψ.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM hprim hnp hs]
  have hp : (mixedDiscriminantScale K:ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (mixedDiscriminantScale_pos K).ne'))
  have hC : (mixedXiNormalization K:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'
  simp only [mul_eq_zero,hp,hC,mixedGammaFactor_ne_zero K hs,false_or]

theorem conductorOneCompleted_ne_zero_right {s : ℂ} (hs : 1 < s.re) :
    ψ.conductorOneCompleted hMtop s ≠ 0 := by
  rw [ψ.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM hprim hnp
    (zero_lt_one.trans hs), ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (mixedDiscriminantScale_pos K).ne')))
    (Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'))
    (mixedGammaFactor_ne_zero K (zero_lt_one.trans hs))) (ψ.dirichlet_ne_zero hs)

theorem conductorOneCompleted_ne_zero : ψ.conductorOneCompleted hMtop ≠ 0 := by
  intro h
  exact ψ.conductorOneCompleted_ne_zero_right hMtop hM hprim hnp (s := 2) (by norm_num)
    (congrFun h 2)

theorem conductorOneCompleted_zero_strip {s : ℂ}
    (hs : ψ.conductorOneCompleted hMtop s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra h
    have hr : 1 < (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
    have hW : mixedClassRootNumber K (ψ.conductorOneClassCharacter hMtop) ≠ 0 := by
      intro hz
      have H := ψ.conductorOneCompleted_rootNumber_norm hMtop
      rw [hz,norm_zero] at H
      exact zero_ne_one H
    exact (mul_ne_zero hW (ψ.inverse.conductorOneCompleted_ne_zero_right hMtop hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hr))
      ((ψ.conductorOneCompleted_functional_equation hMtop hnp s).symm.trans hs)
  · by_contra h
    exact ψ.conductorOneCompleted_ne_zero_right hMtop hM hprim hnp (lt_of_not_ge h) hs

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
