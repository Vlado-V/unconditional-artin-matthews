module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnified
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

/-! Multiplicity transfer for the unified primitive completion. The
local analytic unit is exactly the genuine conductor power times mixed Gamma,
including the normalized conductor-one branch. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set Filter
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveCompletedUnified_analyticOrderAt_eq_primitive
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (ψ.primitiveCompletedUnified hM) s =
      analyticOrderAt (ψ.primitiveContinued hM hprim) s := by
  let A : ℂ := (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)
  have hA : A ≠ 0 := Complex.ofReal_ne_zero.mpr
    (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'
  let U : ℂ → ℂ := fun z => A^z * mixedGammaFactor K z
  have hG : AnalyticAt ℂ (mixedGammaFactor K) s :=
    (mixedGammaFactor_differentiableOn K).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re) s hs
  have hU : AnalyticAt ℂ U s :=
    ((differentiable_id.const_cpow (Or.inl hA)).analyticAt s).mul hG
  have hU0 : U s ≠ 0 := mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hA)) (mixedGammaFactor_ne_zero K hs)
  have he : ψ.primitiveCompletedUnified hM =ᶠ[𝓝 s]
      U * ψ.primitiveContinued hM hprim := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ψ.primitiveCompletedUnified_eq_gamma_primitive hM hprim hnp hz
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul hU ((ψ.primitiveContinued_entire hM hprim).analyticAt s),
    hU.analyticOrderAt_eq_zero.mpr hU0,zero_add]

theorem primitiveCompletedUnified_analyticOrderNatAt_eq_primitive
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt (ψ.primitiveCompletedUnified hM) s =
      analyticOrderNatAt (ψ.primitiveContinued hM hprim) s := by
  unfold analyticOrderNatAt
  rw [ψ.primitiveCompletedUnified_analyticOrderAt_eq_primitive hM hprim hnp hs]

theorem primitiveCompletedUnified_meromorphicOrderAt_eq_primitive
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (ψ.primitiveCompletedUnified hM) s =
      meromorphicOrderAt (ψ.primitiveContinued hM hprim) s := by
  rw [((ψ.primitiveCompletedUnified_entire hM hprim).analyticAt s).meromorphicOrderAt_eq,
    ((ψ.primitiveContinued_entire hM hprim).analyticAt s).meromorphicOrderAt_eq,
    ψ.primitiveCompletedUnified_analyticOrderAt_eq_primitive hM hprim hnp hs]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
