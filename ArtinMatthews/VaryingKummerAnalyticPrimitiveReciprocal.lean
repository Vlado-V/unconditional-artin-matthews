module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealLog
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
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

/-! A conductor-independent reciprocal bound obtained from the actual
ideal Euler logarithm. Its constant depends only on the degree of the field;
no zero exclusion outside absolute convergence is used. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set
open scoped NumberField nonZeroDivisors Classical
noncomputable section

def primitiveReciprocalBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.exp ((Module.finrank ℚ K:ℝ)*dedekindEulerLogConstant)

theorem primitiveReciprocalBound_pos (K : Type*) [Field K] [NumberField K] :
    0 < primitiveReciprocalBound K := Real.exp_pos _

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem dirichlet_inv_eq_exp_neg_eulerLog {s : ℂ} (hs : 1 < s.re) :
    (ψ.dirichlet s)⁻¹ = Complex.exp (-ψ.eulerLog s) := by
  rw [Complex.exp_neg,ψ.exp_eulerLog_eq_dirichlet hs]

theorem dirichlet_inv_norm_le {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖(ψ.dirichlet s)⁻¹‖ ≤ primitiveReciprocalBound K := by
  rw [ψ.dirichlet_inv_eq_exp_neg_eulerLog (by linarith),Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hRe := Complex.re_le_norm (-ψ.eulerLog s)
  simp only [Complex.neg_re,norm_neg] at hRe
  exact hRe.trans (ψ.eulerLog_norm_le hs)

variable (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)

def primitiveReciprocal (s : ℂ) : ℂ := (ψ.primitiveContinued hM hprim s)⁻¹

variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveReciprocal_eq_exp_neg_eulerLog {s : ℂ} (hs : 1 < s.re) :
    ψ.primitiveReciprocal hM hprim s = Complex.exp (-ψ.eulerLog s) := by
  rw [primitiveReciprocal,ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs]
  exact ψ.dirichlet_inv_eq_exp_neg_eulerLog hs

theorem primitiveReciprocal_norm_le {s : ℂ} (hs : 5/4 ≤ s.re) :
    ‖ψ.primitiveReciprocal hM hprim s‖ ≤ primitiveReciprocalBound K := by
  rw [primitiveReciprocal,ψ.primitiveContinued_eq_dirichlet hM hprim hnp (by linarith)]
  exact ψ.dirichlet_inv_norm_le hs

theorem primitiveReciprocal_differentiableAt {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (ψ.primitiveReciprocal hM hprim) s :=
  (ψ.primitiveContinued_entire hM hprim s).inv
    (ψ.primitiveContinued_ne_zero_right hM hprim hnp hs)

theorem primitiveReciprocal_differentiableOn :
    DifferentiableOn ℂ (ψ.primitiveReciprocal hM hprim) {s : ℂ | 1 < s.re} :=
  fun _ hs => (ψ.primitiveReciprocal_differentiableAt hM hprim hnp hs).differentiableWithinAt

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
