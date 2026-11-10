module

public import ArtinMatthews.EisensteinAngularCyclotomic
public import ArtinMatthews.SIntegerResidueGauss
public import ArtinMatthews.SIntegerStandardPhase
public import ArtinMatthews.StandardAdelicWeilIndex
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
public import ArtinMatthews.SourceGeneratorWeil
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
public import Mathlib.Tactic.PNatToNat
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cyclotomic angular sextic character in the source residue
phase has cubic Gauss factor equal to the actual local analytic Weil
factor. Its literal chi(4) inverse correction is retained. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory
open SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open AngularLambda VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (P : HeightOneSpectrum (𝓞 F))

local instance cycloSourceWeilMeasurable : MeasurableSpace (P.adicCompletion F) := borel (P.adicCompletion F)
local instance cycloSourceWeilBorel : BorelSpace (P.adicCompletion F) := ⟨rfl⟩
local instance cycloSourceWeilQuotientField : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance cycloSourceWeilQuotientFinite : Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance cycloSourceWeilQuotientFintype : Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

omit S₀ in
theorem outside_two_of_six (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces F 2 := by
  intro hv
  rw [GlobalClassFieldTheory.Reciprocity.mem_powerResidueExponentFinitePlaces_iff,
    GlobalClassFieldTheory.Reciprocity.powerResidueExponentIdeal, Ideal.dvd_span_singleton] at hv
  have htwo : (2 : 𝓞 F) ∈ P.asIdeal := by simpa using hv
  have h := P.asIdeal.mul_mem_left (3 : 𝓞 F) htwo
  norm_num at h
  exact hsix h

theorem sourceGeneratorWeil_eq_angularGammaThree {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ StandardAdelic.traceBadPlaces F) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    standardNormalizedWeil F (generatorFieldUnit S₀ P a ha)⁻¹ (.inr P) =
      probeGaussGamma (cyclotomicAngularResidueCharacter hζ P hsix)
        (residueSourcePhase S₀ P hP a ha) 3 :=
  sourceGeneratorWeil_eq_sexticGamma F S₀ P hζ hP a ha hbad (outside_two_of_six F P hsix)
    _ (cyclotomicAngularResidueCharacter_order hζ P hsix)

theorem sourceGeneratorWeil_eq_angularTau {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ StandardAdelic.traceBadPlaces F) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    standardNormalizedWeil F (generatorFieldUnit S₀ P a ha)⁻¹ (.inr P) =
      residueSourceTau S₀ P hP a ha ((cyclotomicAngularResidueCharacter hζ P hsix) ^ 3) /
        (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) :=
  sourceGeneratorWeil_eq_tau F S₀ P hζ hP a ha hbad (outside_two_of_six F P hsix)
    _ (cyclotomicAngularResidueCharacter_order hζ P hsix)

theorem sourceGeneratorLocalG_eq_angularWeil {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ StandardAdelic.traceBadPlaces F) (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    (cyclotomicAngularResidueCharacter hζ P hsix (4 : 𝓞 F ⧸ P.asIdeal))⁻¹ *
      (residueSourceTau S₀ P hP a ha ((cyclotomicAngularResidueCharacter hζ P hsix) ^ 3) /
        (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) =
    (cyclotomicAngularResidueCharacter hζ P hsix (4 : 𝓞 F ⧸ P.asIdeal))⁻¹ *
      standardNormalizedWeil F (generatorFieldUnit S₀ P a ha)⁻¹ (.inr P) := by
  rw [sourceGeneratorWeil_eq_angularTau F S₀ P hζ hP a ha hbad hsix]

end

end ArtinMatthews.QuadraticWeil
