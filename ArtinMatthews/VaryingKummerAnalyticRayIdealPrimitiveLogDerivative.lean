module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound
public import ArtinMatthews.VaryingKummerAnalyticRayIdealLogDerivative
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

/-! The actual primitive entire continuation inherits the universal
right-half-plane logarithmic-derivative estimate from its genuine ideal
Euler product. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Set Filter
open scoped NumberField Topology
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveContinued_logDeriv_eq_dirichlet {s : ℂ} (hs : 1 < s.re) :
    logDeriv (ψ.primitiveContinued hM hprim) s = logDeriv ψ.dirichlet s := by
  have heq : ψ.primitiveContinued hM hprim =ᶠ[𝓝 s] ψ.dirichlet := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ψ.primitiveContinued_eq_dirichlet hM hprim hnp hz
  rw [logDeriv_apply,logDeriv_apply,heq.deriv_eq,heq.eq_of_nhds]

theorem primitiveContinued_logDeriv_norm_le {s : ℂ} (hs : (3/2:ℝ) ≤ s.re) :
    ‖logDeriv (ψ.primitiveContinued hM hprim) s‖ ≤
      dedekindLogDerivUniformConstant * (Module.finrank ℚ K:ℝ) := by
  rw [ψ.primitiveContinued_logDeriv_eq_dirichlet hM hprim hnp (by linarith)]
  exact ψ.dirichlet_logDeriv_norm_le hs

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
