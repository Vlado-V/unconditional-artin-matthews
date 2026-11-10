module

public import ArtinMatthews.SourcePrincipalBallQuotientCoverage
public import ArtinMatthews.SIntegerPrincipalExterior
public import ArtinMatthews.SourceFractionalIdealDualValuation
public import ArtinMatthews.SourceFractionalIdealValuation
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The kernel of the actual localized quotient restricted to a finite
ball ideal is the literal product of that ball ideal with the exterior
modulus. The proof uses the actual localization numerator. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀

theorem sourcePrincipalExteriorModulus_count_inS (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) (v : S) :
    FractionalIdeal.count K v.val (M : FI) = 0 := by
  have h := (coprime_denominator_iff_exterior d (principalizingDenominator_ne_zero S₀) M).mp hc v.val v.property
  rw [FractionalIdeal.count_coe K v.val hM, Int.natCast_eq_zero]
  exact not_ne_iff.mp (fun hn => h ((Associates.count_ne_zero_iff_dvd hM v.val.irreducible).mp hn))

theorem sourcePrincipalDenominatorPowers_valuation_exterior (s : Submonoid.powers d)
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) : P.valuation K ((s : 𝓞 K) : K) = 1 := by
  obtain ⟨n, hn⟩ := s.property
  change P.valuation K (algebraMap (𝓞 K) K (s : 𝓞 K)) = 1
  rw [← hn, map_pow, map_pow, sourcePrincipalDenominator_valuation_exterior K S₀ P hP, one_pow]

theorem sourcePrincipalLocalizationNumerator_valuation (x : OS) (r : 𝓞 K)
    (s : Submonoid.powers d)
    (h : x * algebraMap (𝓞 K) OS (s : 𝓞 K) = algebraMap (𝓞 K) OS r)
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) :
    P.valuation K (r : K) = P.valuation K (x : K) := by
  have he : (x : K) * ((s : 𝓞 K) : K) = (r : K) :=
    congrArg (fun a : OS => (a : K)) h
  rw [← he, map_mul, sourcePrincipalDenominatorPowers_valuation_exterior K S₀ s P hP, mul_one]

theorem sourcePrincipalExteriorModulus_mem_iff (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hc : IsCoprime M (Ideal.span {d})) (x : OS) :
    x ∈ M.map (algebraMap (𝓞 K) OS) ↔
      ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
        P.valuation K (x : K) ≤ WithZero.exp (-FractionalIdeal.count K P (M : FI)) := by
  let : IsLocalization.Away d OS := principalIntegerRing_isLocalization S₀
  have hMF : (M : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hM
  constructor
  · intro hx P hP
    obtain ⟨⟨r, s⟩, hr⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers d) OS).mp hx
    have hrI : ((r : M) : 𝓞 K) ∈ M := r.property
    have hv := (sourceFractionalIdeal_mem_iff_valuation K (M : FI) hMF _).mp
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hrI) P
    rw [← sourcePrincipalLocalizationNumerator_valuation K S₀ x (r : 𝓞 K) s hr P hP]
    exact hv
  · intro hx
    obtain ⟨⟨r, s⟩, hr⟩ := IsLocalization.surj (Submonoid.powers d) x
    have hrF : (r : K) ∈ (M : FI) := by
      apply (sourceFractionalIdeal_mem_iff_valuation K (M : FI) hMF _).mpr
      intro P
      by_cases hP : P ∈ S
      · rw [sourcePrincipalExteriorModulus_count_inS K S₀ M hM hc ⟨P, hP⟩,
          neg_zero, WithZero.exp_zero]
        exact P.valuation_le_one (K := K) r
      · rw [sourcePrincipalLocalizationNumerator_valuation K S₀ x r s hr P hP]
        exact hx P hP
    obtain ⟨a, ha, he⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hrF
    have har : a = r := (IsFractionRing.injective (𝓞 K) K) he
    subst a
    exact (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers d) OS).mpr ⟨(⟨r, ha⟩, s), hr⟩

theorem sourcePrincipalExteriorBallProduct_mem_iff (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (x : K) :
    x ∈ (M : FI) * sourceFiniteBallIdeal K S e ↔
      x ∈ sourceFiniteBallIdeal K S e ∧
        ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
          P.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K P (M : FI)) := by
  have hMF : (M : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hM
  have hJ := sourceFiniteBallIdeal_ne_zero K S e
  have hcP (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) :
      FractionalIdeal.count K P ((M : FI) * sourceFiniteBallIdeal K S e) =
        FractionalIdeal.count K P (M : FI) := by
    rw [FractionalIdeal.count_mul K P hMF hJ, sourceFiniteBallIdeal_count K S e,
      dite_eq_right hP, add_zero]
  have hnonneg (P : HeightOneSpectrum (𝓞 K)) : 0 ≤ FractionalIdeal.count K P (M : FI) := by
    rw [FractionalIdeal.count_coe K P hM]
    positivity
  rw [sourceFractionalIdeal_mem_iff_valuation K _ (mul_ne_zero hMF hJ),
    sourceFractionalIdeal_mem_iff_valuation K _ hJ]
  constructor
  · intro h
    have hout (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) :=
      (hcP P hP) ▸ h P
    refine ⟨fun P => ?_, hout⟩
    by_cases hP : P ∈ S
    · rw [sourceFiniteBallIdeal_count K S e, dite_eq_left hP]
      exact (sourceFiniteBallIdeal_product_count_at_S K S e (M : FI) hMF
        (sourcePrincipalExteriorModulus_count_inS K S₀ M hM hc) ⟨P, hP⟩) ▸ h P
    · rw [sourceFiniteBallIdeal_count K S e, dite_eq_right hP]
      exact (hout P hP).trans (WithZero.exp_le_exp.mpr (neg_nonpos.mpr (hnonneg P)))
  · rintro ⟨hin, hout⟩ P
    by_cases hP : P ∈ S
    · rw [sourceFiniteBallIdeal_product_count_at_S K S e (M : FI) hMF
        (sourcePrincipalExteriorModulus_count_inS K S₀ M hM hc) ⟨P, hP⟩]
      simpa only [sourceFiniteBallIdeal_count K S e, dite_eq_left hP] using hin P
    · rw [hcP P hP]
      exact hout P hP

theorem sourcePrincipalBallIdealToQuotient_eq_zero_iff (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (x : sourceFiniteBallIdeal K S e) :
    sourcePrincipalBallIdealToQuotient K S₀ e M x = 0 ↔
      (x : K) ∈ (M : FI) * sourceFiniteBallIdeal K S e := by
  change Ideal.Quotient.mk (M.map (algebraMap (𝓞 K) OS))
    (sourcePrincipalBallIdealToInteger K S₀ e x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, sourcePrincipalExteriorModulus_mem_iff K S₀ M hM hc,
    sourcePrincipalExteriorBallProduct_mem_iff K S₀ e M hM hc, and_iff_right x.property]
  rfl

end
end ArtinMatthews.SourcePhysical
