module

public import ArtinMatthews.SIntegerResidueGauss
public import ArtinMatthews.SourceCRTCofactorPhase
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

/-! Exact residue-field transport for each actual squarefree source
Gauss factor. The standard generator phase and its cofactor are retained. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient
open SIntegerFourier StandardAdelic SourceCRTNormalization
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})

def reflectionLocalPrimeEquiv :
    ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P 1) ≃+* ((𝓞 K) ⧸ P.asIdeal) :=
  (Ideal.quotEquivOfEq (by simpa only [primePowerIdeal, pow_one] using ha)).trans
    (generatorResidueEquiv S₀ P hP a ha)

theorem reflectionLocalPrimeEquiv_mk (x : PrincipalIntegerRing S₀) :
    reflectionLocalPrimeEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x) =
      generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x) := by
  rw [reflectionLocalPrimeEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]

def reflectionLocalPrimeCharacter (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) :
    MulChar ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P 1) ℂ :=
  pullCharacter (reflectionLocalPrimeEquiv S₀ P hP a ha) χ

theorem reflectionLocalPrimeCharacter_weight (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P 1) :
    reflectionLocalPrimeCharacter S₀ P hP a ha χ x =
      sourceLocalPowerWeight S₀ P hP a ha χ 1 x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [reflectionLocalPrimeCharacter, pullCharacter_apply, reflectionLocalPrimeEquiv_mk]
  unfold sourceLocalPowerWeight
  erw [Ideal.quotEquivOfEq_mk (generator_power_ideal S₀ P a ha 1) x]
  rw [generatorPowerWeight, dite_eq_left (show 0 < 1 by decide), generatorResidueReduction_mk,
    pow_one]
  rfl

theorem reflectionLocalPrimePhase :
    sourcePrimePowerPhase S₀ P a ha 1 =
      pullAddChar (reflectionLocalPrimeEquiv S₀ P hP a ha)
        (residueSourcePhase S₀ P hP a ha) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sourcePrimePowerPhase_mk, pow_one, pullAddChar_apply, reflectionLocalPrimeEquiv_mk,
    residueSourcePhase, pullAddChar_apply, RingEquiv.symm_apply_apply, sIntegerQuotientPhase_mk]

theorem reflectionLocalPrimeGauss_eq (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) :
    (∑' x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P 1,
      reflectionLocalPrimeCharacter S₀ P hP a ha χ x * sourcePrimePowerPhase S₀ P a ha 1 x) =
        residueSourceTau S₀ P hP a ha χ := by
  rw [reflectionLocalPrimePhase S₀ P hP a ha]
  unfold reflectionLocalPrimeCharacter residueSourceTau
  simp only [pullCharacter_apply, pullAddChar_apply]
  exact (reflectionLocalPrimeEquiv S₀ P hP a ha).toEquiv.tsum_eq
    (fun x => χ x * residueSourcePhase S₀ P hP a ha x)

theorem reflectionLocalPrimeGauss_norm (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : χ ≠ 1) (hbad : P ∉ traceBadPlaces K) :
    ‖∑' x : (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P 1,
      reflectionLocalPrimeCharacter S₀ P hP a ha χ x * sourcePrimePowerPhase S₀ P a ha 1 x‖ =
      Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) := by
  rw [reflectionLocalPrimeGauss_eq]
  exact residueSourceTau_norm S₀ P hP a ha hbad χ hχ

end
end ArtinMatthews.VaryingKummerAnalytic
