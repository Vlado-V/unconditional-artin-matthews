module

public import ArtinMatthews.ArtinRayNormConductor
public import ArtinMatthews.ArtinAbelianLocalFactors
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity
public import ArtinMatthews.PrincipalAngularCorrection
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact norm-conductor mask equals the genuine inertia-fixed
Artin mask for a faithful character, at every finite prime. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain AbelianLocal
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField Classical IsMulCommutative
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ)

include hχ

theorem faithful_inertia_iff_unramified (P : HeightOneSpectrum (𝓞 K))
    (Q : Ideal.primesOver P.asIdeal (𝓞 L)) :
    Q.val.inertia Gal(L/K) ≤ χ.ker ↔ Algebra.IsUnramifiedAt (𝓞 K) Q.val := by
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.property)
  let : Q.val.LiesOver P.asIdeal := Q.property.2
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) P.asIdeal Q.val
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal Q.val Gal(L/K)] at hcard
  constructor
  · intro h
    have hbot : Q.val.inertia Gal(L/K) = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro σ hσ
      change σ = 1
      apply hχ
      have he : χ σ = 1 := h hσ
      exact he.trans (map_one χ).symm
    have hc : Q.val.ramificationIdx (𝓞 K) = 1 := by
      rw [hbot, Nat.card_unique] at hcard
      exact hcard.symm
    exact Ideal.ramificationIdx_eq_one_iff.mp hc
  · intro hu
    let : Algebra.IsUnramifiedAt (𝓞 K) Q.val := hu
    have hc : Nat.card (Q.val.inertia Gal(L/K)) = 1 :=
      hcard.trans Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    let : Subsingleton (Q.val.inertia Gal(L/K)) := (Nat.card_eq_one_iff_unique.mp hc).1
    intro σ hσ
    have he : σ = 1 := congrArg Subtype.val (Subsingleton.elim
      (⟨σ, hσ⟩ : Q.val.inertia Gal(L/K)) 1)
    exact he ▸ χ.ker.one_mem

omit hχ χ in
theorem abelianNormConductor_prime_coprime_iff_unramified
    (P : HeightOneSpectrum (𝓞 K)) (Q : Ideal.primesOver P.asIdeal (𝓞 L)) :
    IsCoprime P.asIdeal (abelianNormConductorIdeal K L) ↔
      Algebra.IsUnramifiedAt (𝓞 K) Q.val := by
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal (Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.property)
  let : Q.val.LiesOver P.asIdeal := Q.property.2
  have hcop : IsCoprime P.asIdeal (abelianNormConductorIdeal K L) ↔
      P ∉ (integralIdealFiniteModulus (abelianNormConductorIdeal K L)
        (abelianNormConductorIdeal_ne_bot K L)).support := by
    rw [integralIdealFiniteModulus_mem_support]
    constructor
    · intro h hd
      exact P.prime.not_isUnit (h.isUnit_of_dvd' (dvd_refl _) hd)
    · intro h
      exact principalAngular_prime_coprime_of_not_le P _ (fun hm => h (Ideal.dvd_iff_le.mpr hm))
  rw [hcop]
  constructor
  · intro h
    rw [abelianNormConductorIdeal_support, mem_ramifiedBaseFinitePlaces_iff] at h
    by_contra hu
    exact h ⟨⟨Q.val, Q.property.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.property⟩,
      Q.property.2, hu⟩
  · intro hu
    apply Finsupp.notMem_support_iff.mpr
    rw [abelianNormConductorIdeal_modulus,
      ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus,
      ideleClassNormDefiningModulus_apply]
    let : Algebra.IsUnramifiedAt (𝓞 K) Q.val := hu
    let w := chosenFinitePlaceExtension (L := L) P
    let W := finitePlaceExtensionCentre (K := K) (L := L) P w
    let : W.asIdeal.LiesOver P.asIdeal := finitePlaceExtensionCentre_liesOver (K := K) (L := L) P w
    have hidx : W.asIdeal.ramificationIdx (𝓞 K) = Q.val.ramificationIdx (𝓞 K) :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal W.asIdeal Gal(L/K)).symm.trans
        (Ideal.ramificationIdxIn_eq_ramificationIdx P.asIdeal Q.val Gal(L/K))
    have hW : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
      Ideal.ramificationIdx_eq_one_iff.mp
        (hidx.trans Ideal.ramificationIdx_eq_one_of_isUnramifiedAt)
    exact ideleClassNormLocalHigherUnitExponent_eq_zero_of_chosenUnramified P
      (chosenFinitePlaceIsUnramified_of_isUnramifiedAt P hW)

variable [IsTotallyComplex K]

theorem abelianNormConductorRayCharacter_primeCoefficient (P : HeightOneSpectrum (𝓞 K)) :
    (abelianNormConductorRayCharacter K L χ).allCoefficient P.asIdeal =
      if (abelianPrimeAbove K L P).val.inertia Gal(L/K) ≤ χ.ker then
        (χ (abelianPrimeFrobenius K L P) : ℂ) else 0 := by
  have hi := faithful_inertia_iff_unramified χ hχ P (abelianPrimeAbove K L P)
  have hc := abelianNormConductor_prime_coprime_iff_unramified P (abelianPrimeAbove K L P)
  unfold EvenIdealRayCharacter.allCoefficient
  rw [dite_eq_left P.ne_bot]
  by_cases h : (abelianPrimeAbove K L P).val.inertia Gal(L/K) ≤ χ.ker
  · rw [ite_eq_left h, ite_eq_left (hc.mpr (hi.mp h)), abelianNormConductorRayCharacter_idealHom]
    exact congrArg Units.val (GaloisIdealCharacter.idealHom_prime_frobenius_of_inertia_le_ker K L χ P
      (abelianPrimeAbove K L P).val (abelianPrimeAbove K L P).property.2.over.symm h
      (abelianPrimeFrobenius K L P) (abelianPrimeFrobenius_spec K L P))
  · rw [ite_eq_right h, ite_eq_right (fun hc' => h (hi.mpr (hc.mp hc')))]

theorem abelianNormConductorRayCharacter_localFactor (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    abelianArtinLocalFactor K L χ P s =
      (1 - (abelianNormConductorRayCharacter K L χ).allCoefficient P.asIdeal *
        (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [abelianNormConductorRayCharacter_primeCoefficient χ hχ, abelianArtinLocalFactor]
  split_ifs <;> simp only [zero_mul, sub_zero, inv_one]

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
