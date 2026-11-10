module

public import ArtinMatthews.SIntegerSourceSexticF
public import ArtinMatthews.SIntegerExteriorGenerator
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The actual CRT additive component of the standard source phase.
Its inverse cofactor is a proved unit of the local quotient; no global
S-integer unit or phase compatibility is assumed. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourcePrimeCofactor (a : ι → PrincipalIntegerRing S₀) (n : ι → ℕ) (i : ι) :
    PrincipalIntegerRing S₀ := ∏ j ∈ Finset.univ.erase i, a j ^ n j

theorem sourcePrimeCofactor_product (a : ι → PrincipalIntegerRing S₀) (n : ι → ℕ) (i : ι) :
    a i ^ n i * sourcePrimeCofactor S₀ a n i = ∏ j, a j ^ n j := by
  exact Finset.mul_prod_erase Finset.univ (fun j => a j ^ n j) (Finset.mem_univ i)

theorem sourcePrimeCofactor_ne_zero (P : ι → HeightOneSpectrum (𝓞 K))
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) : sourcePrimeCofactor S₀ a n i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact pow_ne_zero (n j) (exterior_generator_ne_zero S₀ (P j) (a j) (ha j))

theorem sourcePrimeCofactor_other_mem (P : ι → HeightOneSpectrum (𝓞 K))
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i j : ι) (hji : j ≠ i) :
    sourcePrimeCofactor S₀ a n i ∈ primePowerIdeal S₀ (P j) (n j) := by
  rw [primePowerIdeal, generator_power_ideal S₀ (P j) (a j) (ha j), Ideal.mem_span_singleton]
  exact Finset.dvd_prod_of_mem (fun j => a j ^ n j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

def sourcePrimeComponent (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) : AddChar ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P i) (n i)) ℂ :=
  probeCRTAddCharComponent (fun j => (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P j) (n j))
    (primeCRTEquiv S₀ P n hP)
    (sourceCRTPhase S₀ P n (∏ j, a j ^ n j) (generatorProduct_ne_zero S₀ P a ha n)
      (crtModulus_generator S₀ P n a ha)) i

def sourcePrimePowerPhase (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ P n) ℂ :=
  pullAddChar (Ideal.quotEquivOfEq (generator_power_ideal S₀ P a ha n))
    (sIntegerQuotientPhase K (principalizingSet S₀) (a ^ n)
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha)))

theorem sourcePrimePowerPhase_mk (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (x : PrincipalIntegerRing S₀) :
    sourcePrimePowerPhase S₀ P a ha n (Ideal.Quotient.mk _ x) =
      sCharacter K (principalizingSet S₀) ((x : K) / (a : K) ^ n) := by
  rw [sourcePrimePowerPhase, pullAddChar_apply]
  erw [Ideal.quotEquivOfEq_mk]
  rw [sIntegerQuotientPhase_mk]
  rfl

theorem sourcePrimeComponent_on_cofactor (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (i : ι) (x : PrincipalIntegerRing S₀) :
    sourcePrimeComponent S₀ P hP a ha n i
        (Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a n i * x)) =
      sourcePrimePowerPhase S₀ (P i) (a i) (ha i) (n i) (Ideal.Quotient.mk _ x) := by
  let Ψ := sourceCRTPhase S₀ P n (∏ j, a j ^ n j) (generatorProduct_ne_zero S₀ P a ha n)
    (crtModulus_generator S₀ P n a ha)
  have hf := probeCRTAddChar_factor
    (fun j => (PrincipalIntegerRing S₀) ⧸ primePowerIdeal S₀ (P j) (n j))
    (primeCRTEquiv S₀ P n hP) Ψ
    (Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a n i * x))
  change Ψ (Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a n i * x)) =
    ∏ j, sourcePrimeComponent S₀ P hP a ha n j
      (primeCRTEquiv S₀ P n hP (Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a n i * x)) j) at hf
  simp only [primeCRTEquiv_mk] at hf
  have hp : (∏ j, sourcePrimeComponent S₀ P hP a ha n j
      (Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a n i * x))) =
      sourcePrimeComponent S₀ P hP a ha n i
        (Ideal.Quotient.mk _ (sourcePrimeCofactor S₀ a n i * x)) := by
    apply Finset.prod_eq_single i
    · intro j _ hji
      have hm := (primePowerIdeal S₀ (P j) (n j)).mul_mem_right x
        (sourcePrimeCofactor_other_mem S₀ P a ha n i j hji)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, AddChar.map_zero_eq_one]
    · simp
  rw [hp] at hf
  rw [← hf, sourcePrimePowerPhase_mk]
  change sCharacter K (principalizingSet S₀)
    (((sourcePrimeCofactor S₀ a n i : PrincipalIntegerRing S₀) : K) * (x : K) /
      ((∏ j, a j ^ n j : PrincipalIntegerRing S₀) : K)) = _
  have hc : ((sourcePrimeCofactor S₀ a n i : PrincipalIntegerRing S₀) : K) ≠ 0 :=
    fun h => sourcePrimeCofactor_ne_zero S₀ P a ha n i (Subtype.ext h)
  rw [← sourcePrimeCofactor_product S₀ a n i]
  congr 1
  change ((sourcePrimeCofactor S₀ a n i : PrincipalIntegerRing S₀) : K) * (x : K) /
    ((a i : K) ^ n i * ((sourcePrimeCofactor S₀ a n i : PrincipalIntegerRing S₀) : K)) = _
  field_simp

end
end ArtinMatthews.SourceCRTNormalization
