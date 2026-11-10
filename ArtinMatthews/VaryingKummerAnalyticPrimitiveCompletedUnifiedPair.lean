module

public import ArtinMatthews.VaryingKummerAnalyticPairedCompleted
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnified
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedAnalytic
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletedUnifiedMultiplicity
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

/-! The product of the genuine unified completion and its inverse-character
completion. Its self-reflection is derived from the actual inverse-character
functional equation; neither factor is assumed to reflect into itself. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField ArtinMatthews.ReusedGrowth
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

def primitiveCompletedUnifiedPair : ℂ → ℂ :=
  pairedCompleted (ψ.primitiveCompletedUnified hM) (ψ.inverse.primitiveCompletedUnified hM)

theorem primitiveCompletedUnifiedPair_apply (s : ℂ) :
    ψ.primitiveCompletedUnifiedPair hM s =
      ψ.primitiveCompletedUnified hM s * ψ.inverse.primitiveCompletedUnified hM s := rfl

theorem primitiveCompletedUnifiedPair_zero_iff (s : ℂ) :
    ψ.primitiveCompletedUnifiedPair hM s = 0 ↔
      ψ.primitiveCompletedUnified hM s = 0 ∨ ψ.inverse.primitiveCompletedUnified hM s = 0 :=
  pairedCompleted_zero_iff s

theorem primitiveCompletedUnifiedPair_ne_zero_iff (s : ℂ) :
    ψ.primitiveCompletedUnifiedPair hM s ≠ 0 ↔
      ψ.primitiveCompletedUnified hM s ≠ 0 ∧ ψ.inverse.primitiveCompletedUnified hM s ≠ 0 :=
  pairedCompleted_ne_zero_iff s

variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
include hprim

theorem primitiveCompletedUnifiedPair_entire :
    Differentiable ℂ (ψ.primitiveCompletedUnifiedPair hM) :=
  pairedCompleted_entire (ψ.primitiveCompletedUnified_entire hM hprim)
    (ψ.inverse.primitiveCompletedUnified_entire hM (ψ.inverse_isPrimitive hM hprim))

theorem primitiveCompletedUnifiedPair_hasSubquadraticGrowth :
    HasSubquadraticGrowth (ψ.primitiveCompletedUnifiedPair hM) :=
  pairedCompleted_hasSubquadraticGrowth (ψ.primitiveCompletedUnified_hasSubquadraticGrowth hM hprim)
    (ψ.inverse.primitiveCompletedUnified_hasSubquadraticGrowth hM (ψ.inverse_isPrimitive hM hprim))

theorem primitiveCompletedUnifiedPair_analyticOrderAt (s : ℂ) :
    analyticOrderAt (ψ.primitiveCompletedUnifiedPair hM) s =
      analyticOrderAt (ψ.primitiveCompletedUnified hM) s +
        analyticOrderAt (ψ.inverse.primitiveCompletedUnified hM) s :=
  pairedCompleted_analyticOrderAt (ψ.primitiveCompletedUnified_entire hM hprim)
    (ψ.inverse.primitiveCompletedUnified_entire hM (ψ.inverse_isPrimitive hM hprim)) s

theorem primitiveCompletedUnifiedPair_meromorphicOrderAt (s : ℂ) :
    meromorphicOrderAt (ψ.primitiveCompletedUnifiedPair hM) s =
      meromorphicOrderAt (ψ.primitiveCompletedUnified hM) s +
        meromorphicOrderAt (ψ.inverse.primitiveCompletedUnified hM) s :=
  pairedCompleted_meromorphicOrderAt (ψ.primitiveCompletedUnified_entire hM hprim)
    (ψ.inverse.primitiveCompletedUnified_entire hM (ψ.inverse_isPrimitive hM hprim)) s

theorem primitiveCompletedUnifiedPair_zeroMultiplicity
    (h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0) (s : ℂ) :
    zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) s =
      zeroMultiplicity (ψ.primitiveCompletedUnified hM) s +
        zeroMultiplicity (ψ.inverse.primitiveCompletedUnified hM) s :=
  pairedCompleted_zeroMultiplicity (ψ.primitiveCompletedUnified_entire hM hprim)
    (ψ.inverse.primitiveCompletedUnified_entire hM (ψ.inverse_isPrimitive hM hprim)) h0 s

variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveCompletedUnifiedPair_functionalEquation (s : ℂ) :
    ψ.primitiveCompletedUnifiedPair hM (1-s) = ψ.primitiveCompletedUnifiedPair hM s := by
  obtain ⟨W,_hW,HW⟩ := ψ.primitiveCompletedUnified_functionalEquation hM hprim hnp
  exact pairedCompleted_functionalEquation HW s

theorem primitiveCompletedUnifiedPair_conj (s : ℂ) :
    ψ.primitiveCompletedUnifiedPair hM (conj s) =
      conj (ψ.primitiveCompletedUnifiedPair hM s) :=
  pairedCompleted_conj (ψ.primitiveCompletedUnified_inverse_conj hM hprim hnp) s

theorem primitiveCompletedUnifiedPair_ne_zero_right {s : ℂ} (hs : 1 < s.re) :
    ψ.primitiveCompletedUnifiedPair hM s ≠ 0 :=
  mul_ne_zero (ψ.primitiveCompletedUnified_ne_zero_right hM hprim hnp hs)
    (ψ.inverse.primitiveCompletedUnified_ne_zero_right hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hs)

theorem primitiveCompletedUnifiedPair_ne_zero : ψ.primitiveCompletedUnifiedPair hM ≠ 0 := by
  intro h
  exact ψ.primitiveCompletedUnifiedPair_ne_zero_right hM hprim hnp (s := 2) (by norm_num)
    (congrFun h 2)

theorem primitiveCompletedUnifiedPair_zero_strip {s : ℂ}
    (hs : ψ.primitiveCompletedUnifiedPair hM s = 0) : 0 ≤ s.re ∧ s.re ≤ 1 := by
  obtain ⟨W,_hW,HW⟩ := ψ.primitiveCompletedUnified_functionalEquation hM hprim hnp
  exact pairedCompleted_zero_strip HW
    (fun _ h => ψ.primitiveCompletedUnified_ne_zero_right hM hprim hnp h)
    (fun _ h => ψ.inverse.primitiveCompletedUnified_ne_zero_right hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) h) hs

theorem primitiveCompletedUnifiedPair_logDeriv {s : ℂ} (hs : 1 < s.re) :
    logDeriv (ψ.primitiveCompletedUnifiedPair hM) s =
      logDeriv (ψ.primitiveCompletedUnified hM) s +
        logDeriv (ψ.inverse.primitiveCompletedUnified hM) s :=
  pairedCompleted_logDeriv (ψ.primitiveCompletedUnified_entire hM hprim)
    (ψ.inverse.primitiveCompletedUnified_entire hM (ψ.inverse_isPrimitive hM hprim))
    (ψ.primitiveCompletedUnified_ne_zero_right hM hprim hnp hs)
    (ψ.inverse.primitiveCompletedUnified_ne_zero_right hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hs)

theorem primitiveCompletedUnifiedPair_zero_iff_primitive {s : ℂ} (hs : 0 < s.re) :
    ψ.primitiveCompletedUnifiedPair hM s = 0 ↔
      ψ.primitiveContinued hM hprim s = 0 ∨
        ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) s = 0 := by
  rw [ψ.primitiveCompletedUnifiedPair_zero_iff hM,
    ψ.primitiveCompletedUnified_zero_iff_primitive hM hprim hnp hs,
    ψ.inverse.primitiveCompletedUnified_zero_iff_primitive hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hs]

theorem primitiveCompletedUnifiedPair_analyticOrderAt_eq_primitive
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (ψ.primitiveCompletedUnifiedPair hM) s =
      analyticOrderAt (ψ.primitiveContinued hM hprim) s +
        analyticOrderAt (ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)) s := by
  rw [ψ.primitiveCompletedUnifiedPair_analyticOrderAt hM hprim,
    ψ.primitiveCompletedUnified_analyticOrderAt_eq_primitive hM hprim hnp hs,
    ψ.inverse.primitiveCompletedUnified_analyticOrderAt_eq_primitive hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hs]

theorem primitiveCompletedUnifiedPair_meromorphicOrderAt_eq_primitive
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (ψ.primitiveCompletedUnifiedPair hM) s =
      meromorphicOrderAt (ψ.primitiveContinued hM hprim) s +
        meromorphicOrderAt (ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)) s := by
  rw [ψ.primitiveCompletedUnifiedPair_meromorphicOrderAt hM hprim,
    ψ.primitiveCompletedUnified_meromorphicOrderAt_eq_primitive hM hprim hnp hs,
    ψ.inverse.primitiveCompletedUnified_meromorphicOrderAt_eq_primitive hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hs]

theorem primitiveCompletedUnifiedPair_zeroMultiplicity_eq_primitive
    (h0 : ψ.primitiveCompletedUnifiedPair hM 0 ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    zeroMultiplicity (ψ.primitiveCompletedUnifiedPair hM) s =
      zeroMultiplicity (ψ.primitiveContinued hM hprim) s +
        zeroMultiplicity (ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)) s := by
  rw [ψ.primitiveCompletedUnifiedPair_zeroMultiplicity hM hprim h0]
  unfold zeroMultiplicity
  rw [ψ.primitiveCompletedUnified_meromorphicOrderAt_eq_primitive hM hprim hnp hs,
    ψ.inverse.primitiveCompletedUnified_meromorphicOrderAt_eq_primitive hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hnp) hs]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
