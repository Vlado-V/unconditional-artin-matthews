module

public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SIntegerSourceSexticF
public import ArtinMatthews.FiniteSupportEulerPrefix
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCoefficients
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

/-! Support-independent literal S-integer sextic weights. Adding any
finite set of absent prime moduli contributes factors one. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

private theorem localPowerWeight_norm_le_one
    (T : Finset (HeightOneSpectrum (𝓞 F))) (P : HeightOneSpectrum (𝓞 F))
    (hP : P ∉ principalizingSet T) (a : PrincipalIntegerRing T)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing T)) = Ideal.span {a})
    (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ) (n : ℕ)
    (x : (PrincipalIntegerRing T) ⧸ primePowerIdeal T P n) :
    ‖sourceLocalPowerWeight T P hP a ha χ n x‖ ≤ 1 := by
  unfold sourceLocalPowerWeight
  rw [generatorPowerWeight_eq_transport]
  unfold VaryingKummerAnalytic.probePowerResidueWeight
  split_ifs
  · exact VaryingKummerAnalytic.finiteMulChar_norm_le_one _ _
  · exact (norm_one (α := ℂ)).le

def sourcePrimeExponentLocalWeight
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (P : SourceExteriorPrime F S₀) (n : ℕ) (x : sourceRing F S₀) : ℂ :=
  sourceLocalPowerWeight (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (χ P) n (Ideal.Quotient.mk _ x)

theorem sourcePrimeExponentLocalWeight_zero
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (P : SourceExteriorPrime F S₀) (x : sourceRing F S₀) :
    sourcePrimeExponentLocalWeight F hζ S₀ χ P 0 x = 1 := rfl

def sourcePrimeExponentWeight
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (e : SourcePrimeExponents F S₀) (x : sourceRing F S₀) : ℂ :=
  e.prod fun P n => sourcePrimeExponentLocalWeight F hζ S₀ χ P n x

theorem sourcePrimeExponentWeight_prefix
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (e : SourcePrimeExponents F S₀) (x : sourceRing F S₀)
    (T : Finset (SourceExteriorPrime F S₀)) (he : e.support ⊆ T) :
    sourcePrimeExponentWeight F hζ S₀ χ e x =
      ∏ P ∈ T, sourcePrimeExponentLocalWeight F hζ S₀ χ P (e P) x :=
  SourceEuler.finiteChoiceWeight_eq_prefix
    (fun P n => sourcePrimeExponentLocalWeight F hζ S₀ χ P n x)
    (fun P => sourcePrimeExponentLocalWeight_zero F hζ S₀ χ P x) T e he

theorem sourcePrimeExponentWeight_eq_sourceSexticWeight
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (e : SourcePrimeExponents F S₀) (x : sourceRing F S₀)
    (T : Finset (SourceExteriorPrime F S₀)) (he : e.support ⊆ T) :
    sourcePrimeExponentWeight F hζ S₀ χ e x =
      sourceSexticWeight (sourceHilbertSeed F S₀) (fun P : T => P.val.val)
        (fun P => P.val.property) (fun P => sourceAllowedPrimeGenerator F hζ S₀ P.val)
        (fun P => sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val)
        (fun P => χ P.val) (fun P => e P.val) x := by
  rw [sourcePrimeExponentWeight_prefix F hζ S₀ χ e x T he]
  exact (Finset.prod_coe_sort T _).symm

theorem sourcePrimeExponentLocalWeight_norm_le_one
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (P : SourceExteriorPrime F S₀) (n : ℕ) (x : sourceRing F S₀) :
    ‖sourcePrimeExponentLocalWeight F hζ S₀ χ P n x‖ ≤ 1 :=
  localPowerWeight_norm_le_one F (sourceHilbertSeed F S₀) P.val P.property _
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) (χ P) n _

theorem sourcePrimeExponentWeight_norm_le_one
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (e : SourcePrimeExponents F S₀) (x : sourceRing F S₀) :
    ‖sourcePrimeExponentWeight F hζ S₀ χ e x‖ ≤ 1 := by
  rw [sourcePrimeExponentWeight, Finsupp.prod, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun P _ => sourcePrimeExponentLocalWeight_norm_le_one F hζ S₀ χ P (e P) x)

end
end ArtinMatthews
