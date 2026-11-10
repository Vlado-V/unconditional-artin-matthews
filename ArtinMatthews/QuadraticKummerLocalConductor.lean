module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ArtinMatthews.QuadraticKummer
public import ArtinMatthews.QuadraticKummerLocalSquare
public import Mathlib.Data.Nat.Choose.Multinomial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Local squares have zero exponent in the actual quadratic norm conductor. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 6)

include hζ

theorem quadraticKummer_localHigherUnitExponent_eq_zero_of_localSquare
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hsquare : ∃ s : v.adicCompletion F,
      s ^ 2 = algebraMap F (v.adicCompletion F) (u : F)) :
    ideleClassNormLocalHigherUnitExponent (K := F) (L := QuadraticKummerField u) v = 0 := by
  apply (ideleClassNormLocalHigherUnitExponent_eq_zero_iff v).mpr
  rw [quadraticKummer_localNormSubgroup_eq_top_of_localSquare hζ u v hsquare]
  exact le_top

theorem quadraticKummer_conductorExponent_eq_zero_of_localSquare
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hsquare : ∃ s : v.adicCompletion F,
      s ^ 2 = algebraMap F (v.adicCompletion F) (u : F)) :
    ideleClassNormNarrowFiniteConductor (K := F) (L := QuadraticKummerField u) v = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (ideleClassNorm_narrowFiniteConductor_apply_le_localHigherUnitExponent
    (K := F) (L := QuadraticKummerField u) v).trans_eq
      (quadraticKummer_localHigherUnitExponent_eq_zero_of_localSquare hζ u v hsquare)

theorem quadraticKummer_not_mem_conductorSupport_of_localSquare
    (u : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hsquare : ∃ s : v.adicCompletion F,
      s ^ 2 = algebraMap F (v.adicCompletion F) (u : F)) :
    v ∉ (ideleClassNormNarrowFiniteConductor (K := F) (L := QuadraticKummerField u)).support := by
  simpa only [Finsupp.mem_support_iff, not_not] using
    quadraticKummer_conductorExponent_eq_zero_of_localSquare hζ u v hsquare

end
end ArtinMatthews
