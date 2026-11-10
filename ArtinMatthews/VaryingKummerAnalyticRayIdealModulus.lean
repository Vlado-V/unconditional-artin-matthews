module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import ArtinMatthews.VaryingKummerAnalyticRayCompletedCongruence
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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

/-! A genuine integral ideal as a full even ray modulus, with exact support
and prime-power exponents. Local fractional congruences recover the actual
integral ideal congruence after denominator clearing. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def integralIdealFiniteModulus (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) : FiniteModulus K :=
  Finsupp.ofSupportFinite (fun v : HeightOneSpectrum (𝓞 K) => multiplicity v.asIdeal M)
    ((Ideal.finite_factors hM).subset fun _v hv => dvd_of_multiplicity_pos (Nat.pos_of_ne_zero hv))

def integralIdealRayModulus (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) : Modulus K :=
  Modulus.ofFinite (integralIdealFiniteModulus M hM)

theorem integralIdealFiniteModulus_apply (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 K)) :
    integralIdealFiniteModulus M hM v = multiplicity v.asIdeal M := rfl

theorem integralIdealFiniteModulus_mem_support (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ (integralIdealFiniteModulus M hM).support ↔ v.asIdeal ∣ M := by
  rw [Finsupp.mem_support_iff,integralIdealFiniteModulus_apply]
  exact multiplicity_ne_zero (FiniteMultiplicity.of_prime_left v.prime hM)

theorem integralIdealRayModulus_antitone {M f : Ideal (𝓞 K)}
    (hM : M ≠ ⊥) (hf : f ≠ ⊥) (hMf : M ≤ f) :
    integralIdealRayModulus f hf ≤ integralIdealRayModulus M hM := by
  constructor
  · intro v
    exact v.multiplicity_le_of_ideal_ge hMf hM
  · exact Finset.Subset.refl _

theorem integralIdeal_mem_iff_modulus_prime_powers (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (a : 𝓞 K) :
    a ∈ M ↔ ∀ v ∈ (integralIdealFiniteModulus M hM).support,
      a ∈ v.asIdeal^(integralIdealFiniteModulus M hM v) := by
  have he : (⨅ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal^(integralIdealFiniteModulus M hM v)) = M := by
    simpa only [integralIdealFiniteModulus_apply,
      HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hM] using Ideal.iInf_maxPowDividing_eq hM
  nth_rw 1 [← he]
  rw [Ideal.mem_iInf]
  constructor
  · intro h v _
    exact h v
  · intro h v
    by_cases hv : v ∈ (integralIdealFiniteModulus M hM).support
    · exact h v hv
    · rw [Finsupp.notMem_support_iff.mp hv,pow_zero,Ideal.one_eq_top]
      trivial

theorem principal_idealRayModulus_valuation_one (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (x : Kˣ) (hx : IdeleGroup.principalIdele K x ∈
      idelePrimeToModulusSubgroup (integralIdealRayModulus M hM))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ M) :
    v.valuation K (x:K) = 1 :=
  principal_local_higherUnit_valuation_one v _ x
    (hx.2 v ((integralIdealFiniteModulus_mem_support M hM v).mpr hv))

theorem principal_idealRayModulus_integral_difference (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (x : Kˣ) (hx : IdeleGroup.principalIdele K x ∈
      idelePrimeToModulusSubgroup (integralIdealRayModulus M hM))
    (a b : 𝓞 K) (hab : (b:K)*(x:K)=(a:K)) : a-b ∈ M := by
  apply (integralIdeal_mem_iff_modulus_prime_powers M hM (a-b)).mpr
  intro v hv
  exact principal_local_higherUnit_integral_difference v _ x (hx.2 v hv) a b hab

end
end ArtinMatthews.VaryingKummerAnalytic
