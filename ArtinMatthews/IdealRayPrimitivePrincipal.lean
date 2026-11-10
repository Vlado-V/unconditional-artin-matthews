module

public import ArtinMatthews.IdealRayPrimitiveDescent
public import ArtinMatthews.VaryingKummerAnalyticRayFractionalDenominatorCount
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

/-! The descended ideal-modulus character has the genuine principal law
at the smaller conductor. Prime-to-M denominators, not chosen values at
removed bad primes, determine the extension. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace EvenIdealRayCharacter
variable {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)


theorem descendedIdealRayCharacter_principal (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : M ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (M) a) =
      if IsUnit (Ideal.Quotient.mk (M) a)
        then φ (Ideal.Quotient.mk f a) else 0)
    (a : 𝓞 K) (ha : a ≠ 0) (hac : IsCoprime (Ideal.span {a}) f) :
    (ψ.descendedIdealRayCharacter hM f hf hMf φ hmask
      (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus f hf))
        (integralPrincipalPrimeToIdeal f hf a ha hac)) : ℂ) = φ (Ideal.Quotient.mk f a) := by
  let m := integralIdealRayModulus M hM
  let n := integralIdealRayModulus f hf
  let hnm : n ≤ m := integralIdealRayModulus_antitone (hM) hf hMf
  let J := integralPrincipalPrimeToIdeal f hf a ha hac
  let q := QuotientGroup.mk' (principalRayIdealSubgroup n)
  obtain ⟨c,hc⟩ := conductorIdealProjection_surjective hM f hf hMf (q J)
  obtain ⟨I,rfl⟩ := QuotientGroup.mk'_surjective _ c
  have hp : q (primeToIdealConductorInclusion hnm I) = q J := by
    rw [← idealConductorProjection_ideal hnm I]
    exact hc
  have hmem : primeToIdealConductorInclusion hnm I / J ∈ principalRayIdealSubgroup n := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (primeToIdealConductorInclusion hnm I / J) = 1
    rw [map_div,hp]
    simp only [div_self']
  obtain ⟨x,hx,hIx⟩ := (mem_principalRayIdealSubgroup_iff n _).mp hmem
  let ua : Kˣ := Units.mk0 (a:K) (by exact_mod_cast ha)
  let y : Kˣ := x * ua
  have hyI : toPrincipalIdeal (𝓞 K) K y = (I:FractionalIdealGroup K) := by
    change toPrincipalIdeal (𝓞 K) K (x*ua) = _
    rw [map_mul,hIx]
    change ((I:FractionalIdealGroup K) / toPrincipalIdeal (𝓞 K) K ua) *
      toPrincipalIdeal (𝓞 K) K ua = _
    exact div_mul_cancel _ _
  have hcounts : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ M →
      FractionalIdeal.count K v (spanSingleton (𝓞 K)⁰ (y:K)) = 0 := by
    intro v hv
    have H := I.property v ((integralIdealFiniteModulus_mem_support _ (hM) v).mpr hv)
    rw [← hyI,coe_toPrincipalIdeal] at H
    exact H
  obtain ⟨b,d,hb,hd,hbc,hdc,hy⟩ := exists_coprime_integral_fraction_of_counts K
    (M) (hM) y hcounts
  have hmul : ((a*d:𝓞 K):K)*(x:K)=(b:K) := by
    have hdK : (d:K) ≠ 0 := by exact_mod_cast hd
    have H : (x:K)*(a:K)=(b:K)/(d:K) := hy
    have H' := (eq_div_iff hdK).mp H
    change ((a:K)*(d:K))*(x:K)=(b:K)
    calc
      ((a:K)*(d:K))*(x:K) = ((x:K)*(a:K))*(d:K) := by ring
      _ = (b:K) := H'
  have hdiff := principal_idealRayModulus_integral_difference f hf x hx b (a*d) hmul
  have he : Ideal.Quotient.mk f b = Ideal.Quotient.mk f a * Ideal.Quotient.mk f d := by
    rw [← map_mul]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem b (a*d)).mpr hdiff
  have hvb := hmask b
  have hvd := hmask d
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ b).mpr hbc)] at hvb
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ d).mpr hdc)] at hvd
  have hdunit : IsUnit (Ideal.Quotient.mk f d) := by
    simpa only [Ideal.Quotient.factor_mk] using
      ((quotient_isUnit_iff_span_coprime _ d).mpr hdc).map (Ideal.Quotient.factor hMf)
  have hval : (ψ.idealHom (I:FractionalIdealGroup K):ℂ) = φ (Ideal.Quotient.mk f a) := by
    rw [← hyI,toPrincipalIdeal_eq_fraction y b d hb hd hy,map_div,Units.val_div_eq_div_val,
      ψ.principalLaw b hb hbc,ψ.principalLaw d hd hdc,hvb,hvd,he,map_mul]
    exact mul_div_cancel_right₀ _ (MulChar.apply_ne_zero_iff.mpr hdunit)
  rw [← hc,ψ.descendedIdealRayCharacter_projection,ψ.rayClassCharacter_ideal]
  exact hval


end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
