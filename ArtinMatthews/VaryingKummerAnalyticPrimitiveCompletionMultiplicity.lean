module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneGammaEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletionIdentity
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

/-! Exact multiplicity transfer from each genuine primitive completion to
its primitive continuation in the positive half-plane. The analytic units
are the actual conductor/discriminant powers and mixed Gamma factor. -/
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

theorem properCompleted_analyticOrderAt_eq_primitive (hMt : M ≠ ⊤)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (ψ.properCompleted hM hMt) s =
      analyticOrderAt (ψ.primitiveContinued hM hprim) s := by
  let A : ℂ := (mixedConductorScale K (integralIdealFractionalUnit M hM) : ℂ)
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
  have he : ψ.properCompleted hM hMt =ᶠ[𝓝 s]
      U * ψ.primitiveContinued hM hprim := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ψ.properCompleted_eq_gamma_primitive_of_re_pos hM hMt hprim hnp hz
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul hU ((ψ.primitiveContinued_entire hM hprim).analyticAt s),
    hU.analyticOrderAt_eq_zero.mpr hU0, zero_add]

theorem properCompleted_analyticOrderNatAt_eq_primitive (hMt : M ≠ ⊤)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt (ψ.properCompleted hM hMt) s =
      analyticOrderNatAt (ψ.primitiveContinued hM hprim) s := by
  unfold analyticOrderNatAt
  rw [ψ.properCompleted_analyticOrderAt_eq_primitive hM hprim hnp hMt hs]

theorem properCompleted_meromorphicOrderAt_eq_primitive (hMt : M ≠ ⊤)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (ψ.properCompleted hM hMt) s =
      meromorphicOrderAt (ψ.primitiveContinued hM hprim) s := by
  rw [((ψ.properCompleted_entire hM hMt hprim).analyticAt s).meromorphicOrderAt_eq,
    ((ψ.primitiveContinued_entire hM hprim).analyticAt s).meromorphicOrderAt_eq,
    ψ.properCompleted_analyticOrderAt_eq_primitive hM hprim hnp hMt hs]

theorem conductorOneCompleted_analyticOrderAt_eq_primitive (hMtop : M = ⊤)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (ψ.conductorOneCompleted hMtop) s =
      analyticOrderAt (ψ.primitiveContinued hM hprim) s := by
  let A : ℂ := (mixedDiscriminantScale K : ℂ)
  have hA : A ≠ 0 := Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'
  let U : ℂ → ℂ := fun z => A^z * (mixedXiNormalization K : ℂ) * mixedGammaFactor K z
  have hG : AnalyticAt ℂ (mixedGammaFactor K) s :=
    (mixedGammaFactor_differentiableOn K).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re) s hs
  have hU : AnalyticAt ℂ U s :=
    (((differentiable_id.const_cpow (Or.inl hA)).analyticAt s).mul analyticAt_const).mul hG
  have hU0 : U s ≠ 0 := mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hA))
    (Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'))
    (mixedGammaFactor_ne_zero K hs)
  have he : ψ.conductorOneCompleted hMtop =ᶠ[𝓝 s]
      U * ψ.primitiveContinued hM hprim := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ψ.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM hprim hnp hz
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul hU ((ψ.primitiveContinued_entire hM hprim).analyticAt s),
    hU.analyticOrderAt_eq_zero.mpr hU0, zero_add]

theorem conductorOneCompleted_analyticOrderNatAt_eq_primitive (hMtop : M = ⊤)
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt (ψ.conductorOneCompleted hMtop) s =
      analyticOrderNatAt (ψ.primitiveContinued hM hprim) s := by
  unfold analyticOrderNatAt
  rw [ψ.conductorOneCompleted_analyticOrderAt_eq_primitive hM hprim hnp hMtop hs]

theorem conductorOneCompleted_meromorphicOrderAt_eq_primitive (hMtop : M = ⊤)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (ψ.conductorOneCompleted hMtop) s =
      meromorphicOrderAt (ψ.primitiveContinued hM hprim) s := by
  rw [((ψ.conductorOneCompleted_entire hMtop).analyticAt s).meromorphicOrderAt_eq,
    ((ψ.primitiveContinued_entire hM hprim).analyticAt s).meromorphicOrderAt_eq,
    ψ.conductorOneCompleted_analyticOrderAt_eq_primitive hM hprim hnp hMtop hs]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
