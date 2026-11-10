module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaConjugation
public import ArtinMatthews.VaryingKummerAnalyticRayIdealConjugation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.Contractible
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

/-! Conjugation of the actual conductor-one completion, proved from the
genuine primitive continuation on the convergent half-plane and entire
uniqueness. The functional equation is not used in this proof. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hMtop : M = ⊤) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hM hprim hnp

theorem conductorOneCompleted_inverse_conj (s : ℂ) :
    ψ.inverse.conductorOneCompleted hMtop (conj s) =
      conj (ψ.conductorOneCompleted hMtop s) := by
  have hp := ψ.conductorOneCompleted_entire hMtop
  have hi := ψ.inverse.conductorOneCompleted_entire hMtop
  have hc : Differentiable ℂ (fun z => conj (ψ.conductorOneCompleted hMtop (conj z))) := by
    intro z
    simpa only [Function.comp_def,starRingEnd_self_apply] using (hp (conj z)).conj_conj
  have he : ψ.inverse.conductorOneCompleted hMtop =
      fun z => conj (ψ.conductorOneCompleted hMtop (conj z)) := by
    apply (hi.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hc.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2:ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    rw [ψ.inverse.conductorOneCompleted_eq_primitiveContinued hMtop hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hz,
      ψ.conductorOneCompleted_eq_primitiveContinued hMtop hM hprim hnp (by simpa using hz)]
    rw [map_mul,map_mul,map_mul]
    rw [← mixedGammaFactor_conj,← positiveReal_cpow_conj (mixedDiscriminantScale_pos K),
      Complex.conj_ofReal]
    simpa only [starRingEnd_self_apply] using
      congrArg (fun v : ℂ => (mixedDiscriminantScale K:ℂ)^z *
        (mixedXiNormalization K:ℂ) * mixedGammaFactor K z * v)
        (ψ.primitiveContinued_inverse_conj hM hprim hnp (conj z))
  simpa only [starRingEnd_self_apply] using congrFun he (conj s)

theorem conductorOneCompleted_inverse_zero_iff (s : ℂ) :
    ψ.inverse.conductorOneCompleted hMtop (conj s) = 0 ↔
      ψ.conductorOneCompleted hMtop s = 0 := by
  rw [ψ.conductorOneCompleted_inverse_conj hMtop hM hprim hnp]
  exact map_eq_zero_iff _ (starRingEnd ℂ).injective

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
