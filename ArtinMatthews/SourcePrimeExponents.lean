module

public import ArtinMatthews.AllowedIntegralGenerator
public import ArtinMatthews.SIntegerStandardPhase
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

/-! Literal finite-support exterior prime coordinates and a fixed actual
allowed generator for each prime. Their ideal, norm and product-generator
maps are derived from the constructed source S-integer PID. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain
open AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F]

abbrev SourceExteriorPrime (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :=
  {P : HeightOneSpectrum (𝓞 F) // P ∉ sourceHilbertSet F S₀}

abbrev SourcePrimeExponents (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :=
  SourceExteriorPrime F S₀ →₀ ℕ

structure SourceAllowedPrimeData {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀) where
  value : sourceRing F S₀
  ne_zero : value ≠ 0
  ideal_eq : P.val.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) = Ideal.span {value}
  allowed : generatorFieldUnit (sourceHilbertSeed F S₀) P.val value ideal_eq ∈ allowedSubgroup F hζ S₀

def sourceAllowedPrimeData {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀) :
    SourceAllowedPrimeData F hζ S₀ P := by
  let I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀)) :=
    ⟨P.val.asIdeal, P.val.ne_bot, by
      simpa only [pow_one] using
        principalPrimePower_coprime (sourceHilbertSeed F S₀) P.val P.property 1⟩
  let hex := exists_exterior_allowed_generator F hζ S₀ I
  exact ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.1,
    hex.choose_spec.choose_spec.2⟩

def sourceAllowedPrimeGenerator {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀) : sourceRing F S₀ :=
  (sourceAllowedPrimeData F hζ S₀ P).value

theorem sourceAllowedPrimeGenerator_ne_zero {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀) :
    sourceAllowedPrimeGenerator F hζ S₀ P ≠ 0 :=
  (sourceAllowedPrimeData F hζ S₀ P).ne_zero

theorem sourceAllowedPrimeGenerator_ideal {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀) :
    P.val.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) =
      Ideal.span {sourceAllowedPrimeGenerator F hζ S₀ P} :=
  (sourceAllowedPrimeData F hζ S₀ P).ideal_eq

def sourceAllowedPrimeUnit {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀) : Fˣ :=
  generatorFieldUnit (sourceHilbertSeed F S₀) P.val
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)

theorem sourceAllowedPrimeUnit_allowed {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : SourceExteriorPrime F S₀) :
    sourceAllowedPrimeUnit F hζ S₀ P ∈ allowedSubgroup F hζ S₀ :=
  (sourceAllowedPrimeData F hζ S₀ P).allowed

def sourcePrimeExponentIdeal (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) : Ideal (𝓞 F) :=
  e.prod fun P n => P.val.asIdeal ^ n

def sourcePrimeExponentNorm (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) : ℕ :=
  e.prod fun P n => Ideal.absNorm P.val.asIdeal ^ n

def sourcePrimeExponentGenerator {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e : SourcePrimeExponents F S₀) : sourceRing F S₀ :=
  e.prod fun P n => sourceAllowedPrimeGenerator F hζ S₀ P ^ n

def sourcePrimeExponentUnit {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e : SourcePrimeExponents F S₀) : Fˣ :=
  e.prod fun P n => sourceAllowedPrimeUnit F hζ S₀ P ^ n

theorem sourcePrimeExponentIdeal_ne_bot (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) : sourcePrimeExponentIdeal F S₀ e ≠ ⊥ := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  exact pow_ne_zero _ P.val.ne_bot

theorem sourcePrimeExponentIdeal_norm (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) :
    Ideal.absNorm (sourcePrimeExponentIdeal F S₀ e) = sourcePrimeExponentNorm F S₀ e := by
  simp only [sourcePrimeExponentIdeal, sourcePrimeExponentNorm, Finsupp.prod, map_prod, map_pow]

theorem sourcePrimeExponentGenerator_ne_zero {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e : SourcePrimeExponents F S₀) :
    sourcePrimeExponentGenerator F hζ S₀ e ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P _
  exact pow_ne_zero _ (sourceAllowedPrimeGenerator_ne_zero F hζ S₀ P)

theorem sourcePrimeExponentUnit_val {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e : SourcePrimeExponents F S₀) :
    (sourcePrimeExponentUnit F hζ S₀ e : F) =
      (sourcePrimeExponentGenerator F hζ S₀ e : F) := by
  simp only [sourcePrimeExponentUnit, sourcePrimeExponentGenerator, Finsupp.prod,
    Units.coe_prod, Units.val_pow_eq_pow_val]
  calc
    _ = ∏ P ∈ e.support, (sourceAllowedPrimeGenerator F hζ S₀ P : F) ^ e P := by
      apply Finset.prod_congr rfl
      intro P _
      exact congrArg (fun x : F => x ^ e P)
        (generatorFieldUnit_val (sourceHilbertSeed F S₀) P.val
          (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P))
    _ = (sourcePrimeExponentGenerator F hζ S₀ e : F) := by
      simp only [sourcePrimeExponentGenerator, Finsupp.prod,
        SubmonoidClass.coe_finsetProd, Subalgebra.coe_pow]

theorem sourcePrimeExponentUnit_allowed {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (e : SourcePrimeExponents F S₀) :
    sourcePrimeExponentUnit F hζ S₀ e ∈ allowedSubgroup F hζ S₀ := by
  apply Subgroup.prod_mem
  intro P _
  exact (allowedSubgroup F hζ S₀).pow_mem (sourceAllowedPrimeUnit_allowed F hζ S₀ P) _

end

end ArtinMatthews
