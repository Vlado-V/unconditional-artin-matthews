module

public import ArtinMatthews.SourceRowIntegralNumerator
public import ArtinMatthews.SLocalNormAlgebra
public import ArtinMatthews.SIntegerNormIdentification
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

/-! The physical S-product norm of the literal frequency equals its
actual exterior ideal norm. The principal quotient and all exterior
orders are attached to the same source S-integer. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain FractionalIdeal AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "R" => sourceRing F S₀
local notation "S" => sourceHilbertSet F S₀

theorem sourceElementExponents_quotient_card (u : R) (hu : u ≠ 0) :
    Nat.card (R ⧸ Ideal.span {u}) = sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) := by
  let E := sourceElementExponents F S₀ u hu
  let J := sourcePrimeExponentIdeal F S₀ E
  have hJ : J.map (algebraMap (𝓞 F) R) = Ideal.span {u} := sourceElementExponents_ideal F S₀ u hu
  rw [← hJ]
  exact (principal_quotient_card (sourceHilbertSeed F S₀) J
    (sourcePrimeExponentIdeal_exterior F S₀ E).2).trans (sourcePrimeExponentIdeal_norm F S₀ E)

theorem sourceRowFieldNorm_eq_frequencyNorm {ζ : F} (hζ : IsPrimitiveRoot ζ 12) (u : R) (hu : u ≠ 0) :
    fieldSNorm F S (sourceRowFieldUnit F S₀ u hu) =
      (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u hu) : ℝ) := by
  let I : (Ideal R)⁰ := ⟨Ideal.span {u}, mem_nonZeroDivisors_iff_ne_zero.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hu)⟩
  have hI : toPrincipalIdeal R F (sourceRowFieldUnit F S₀ u hu) = FractionalIdeal.mk0 F I := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    change spanSingleton R⁰ (sourceRowFieldUnit F S₀ u hu : F) =
      (Ideal.span {u} : FractionalIdeal R⁰ F)
    rw [coeIdeal_span_singleton]
    rfl
  calc
    _ = idealSNorm F hζ S₀ (FractionalIdeal.mk0 F I) :=
      (idealSNorm_eq_of_generator F hζ S₀ _ _ hI).symm
    _ = (Nat.card (R ⧸ Ideal.span {u}) : ℝ) := idealSNorm_integral_card F hζ S₀ I
    _ = _ := congrArg (fun q : ℕ => (q : ℝ)) (sourceElementExponents_quotient_card F S₀ u hu)

end
end ArtinMatthews.SourceEulerAssembly
