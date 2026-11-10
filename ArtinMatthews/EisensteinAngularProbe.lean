module

public import ArtinMatthews.EisensteinAngularPrime
public import ArtinMatthews.ProbeIdealGaussPhase
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
public import OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! Actual general-prime probe values for the global Eisenstein angular
norm pullback. The prime below is the genuine contraction, and the
residue character is the actual norm lift of the Eisenstein sextic
power-residue character. -/
namespace ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic NumberField IsDedekindDomain
open VaryingKummerAnalytic OAI.SevenEighths
open scoped NumberField BigOperators Classical
noncomputable section
variable (F : Type*) [Field F] [NumberField F] [Algebra BaseField F]

def angularPrimeBelow (P : HeightOneSpectrum (𝓞 F)) : Ideal BaseIntegers :=
  P.asIdeal.under BaseIntegers

local instance (P : HeightOneSpectrum (𝓞 F)) : (angularPrimeBelow F P).IsMaximal :=
  Ideal.isMaximal_under_of_isIntegral_of_isMaximal P.asIdeal

local instance (P : HeightOneSpectrum (𝓞 F)) : P.asIdeal.LiesOver (angularPrimeBelow F P) :=
  Ideal.over_under P.asIdeal

omit [NumberField F] in
theorem angularPrimeBelow_good (P : HeightOneSpectrum (𝓞 F))
    (hthree : (3 : 𝓞 F) ∉ P.asIdeal) : lambda ∉ angularPrimeBelow F P := by
  intro hlam
  change algebraMap BaseIntegers (𝓞 F) lambda ∈ P.asIdeal at hlam
  apply hthree
  have he3 : algebraMap BaseIntegers (𝓞 F) (3 : BaseIntegers) = (3 : 𝓞 F) := map_ofNat _ 3
  obtain ⟨u,hu⟩ := (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
  rw [← he3,hu,map_mul]
  exact P.asIdeal.mul_mem_right _ hlam

omit [Algebra BaseField F] [NumberField F] in
theorem prime_not_three_of_not_six (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) : (3 : 𝓞 F) ∉ P.asIdeal := by
  intro h3
  apply hsix
  simpa only [show (3 : 𝓞 F)*2=6 by norm_num] using P.asIdeal.mul_mem_right 2 h3

theorem angularPrimeBelow_char_ne_two (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) : ringChar (BaseIntegers ⧸ angularPrimeBelow F P) ≠ 2 := by
  intro he
  let : Field (BaseIntegers ⧸ angularPrimeBelow F P) := Ideal.Quotient.field _
  have hz : (2 : BaseIntegers ⧸ angularPrimeBelow F P) = 0 := by
    simpa only [he,Nat.cast_ofNat] using (CharP.cast_eq_zero (BaseIntegers ⧸ angularPrimeBelow F P)
      (ringChar (BaseIntegers ⧸ angularPrimeBelow F P)))
  have hm : (2 : BaseIntegers) ∈ angularPrimeBelow F P :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using hz)
  change algebraMap BaseIntegers (𝓞 F) (2 : BaseIntegers) ∈ P.asIdeal at hm
  apply hsix
  simpa only [map_ofNat,show (3 : 𝓞 F)*2=6 by norm_num] using P.asIdeal.mul_mem_left 3 hm

def globalAngularResidueCharacter (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ :=
  angularPrimeSexticCharacter F P.asIdeal (angularPrimeBelow F P)
    (angularPrimeBelow_good F P (prime_not_three_of_not_six F P hsix))

theorem globalAngularResidueCharacter_order (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) : orderOf (globalAngularResidueCharacter F P hsix) = 6 := by
  let : Field ((𝓞 F) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 F) ⧸ P.asIdeal) := Fintype.ofFinite _
  exact complexSexticResidueNormLift_order _ _ _ (angularPrimeBelow_char_ne_two F P hsix)

theorem globalAngularResidueCharacter_power_residue (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) (u : ((𝓞 F) ⧸ P.asIdeal)ˣ) :
    ∃ z : BaseIntegers, globalAngularResidueCharacter F P hsix (u : (𝓞 F) ⧸ P.asIdeal) =
      OAI.ConcreteTraceCRT.eisEmbedding z ∧
      Ideal.Quotient.mk P.asIdeal (algebraMap BaseIntegers (𝓞 F) z) =
        (u : (𝓞 F) ⧸ P.asIdeal)^((Nat.card ((𝓞 F) ⧸ P.asIdeal)-1)/6) := by
  let : Field ((𝓞 F) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 F) ⧸ P.asIdeal) := Fintype.ofFinite _
  let hq := angularPrimeBelow_good F P (prime_not_three_of_not_six F P hsix)
  refine ⟨sexticResidueNormLift (angularPrimeBelow F P) hq ((𝓞 F) ⧸ P.asIdeal) u,rfl,?_⟩
  rw [← Ideal.Quotient.algebraMap_mk_of_liesOver P.asIdeal (angularPrimeBelow F P)]
  exact sexticResidueNormLift_reduce_unit _ _ _ (angularPrimeBelow_char_ne_two F P hsix) u

theorem globalAngularResidueCharacter_gammaTwo (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeIdealGaussGamma F P (globalAngularResidueCharacter F P hsix) 2 ^ 3 =
      -angularNormIdeal F P.asIdeal := by
  let : Field ((𝓞 F) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 F) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 F) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  have h := angularPrime_gammaTwo_cube F P.asIdeal (angularPrimeBelow F P)
    (angularPrimeBelow_good F P (prime_not_three_of_not_six F P hsix))
    (probeIdealResiduePhase F P) (probeIdealResiduePhase_primitive F P)
  simpa only [probeIdealGaussGamma,probeIdealTau,tsum_fintype,probeGaussGamma,
    ProbeGauss.normalizedGauss,gaussSum,hc,globalAngularResidueCharacter] using h

theorem globalAngularResidueCharacter_localLambda (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    probeIdealGaussLocalLambda F P (globalAngularResidueCharacter F P hsix) =
      angularNormIdeal F P.asIdeal := by
  rw [probeIdealGaussLocalLambda,globalAngularResidueCharacter_gammaTwo,neg_neg]

theorem globalAngularResidueCharacter_outsideS (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ P, (6 : 𝓞 F) ∈ P.asIdeal → P ∈ S) (P : HeightOneSpectrum (𝓞 F))
    (hP : P ∉ S) :
    let hsix : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hP (hS P h)
    probeIdealGaussLocalLambda F P (globalAngularResidueCharacter F P hsix) =
      angularNormIdeal F P.asIdeal :=
  globalAngularResidueCharacter_localLambda F P (fun h => hP (hS P h))

omit [Algebra BaseField F] [NumberField F] in
theorem angularFiniteModulus_supported (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ P, (6 : 𝓞 F) ∈ P.asIdeal → P ∈ S) :
    ∀ P : HeightOneSpectrum (𝓞 F), Ideal.span {(3 : 𝓞 F)} ≤ P.asIdeal → P ∈ S := by
  intro P hP
  apply hS P
  have h3 : (3 : 𝓞 F) ∈ P.asIdeal := hP (Ideal.mem_span_singleton_self 3)
  simpa only [show (3 : 𝓞 F)*2=6 by norm_num] using P.asIdeal.mul_mem_right 2 h3

end
end ArtinMatthews.AngularLambda
