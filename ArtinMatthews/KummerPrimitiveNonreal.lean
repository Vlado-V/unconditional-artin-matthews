module

public import ArtinMatthews.ArtinPrimitiveZeroSources
public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.ArtinFrobeniusGoodPrimeSeparation
public import ArtinMatthews.KummerCyclotomicTowerCyclic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Odd q-radical Artin factors are genuinely non-real. This concerns
the actual q-extension, not the degree-six detector rows. It excludes
self-dual character sources, without claiming any analytic zero-free region. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain RayClass
open scoped NumberField Classical IsMulCommutative ComplexConjugate
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem primitiveArtinZeroWitness_coefficient_ne_inverse {s : ℂ}
    (w : PrimitiveArtinZeroWitness K L s) (hc : w.character ≠ w.character⁻¹) :
    w.primitiveCharacter.coefficient ≠ w.primitiveCharacter.inverse.coefficient := by
  intro he
  apply hc
  let M := rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)
  have hM : M ≠ ⊥ := rationalModulusIdeal_ne_bot _
  have hvalue (v : HeightOneSpectrum (𝓞 K)) (hv : IsCoprime v.asIdeal M) :
      w.primitiveCharacter.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) =
        w.character (GaloisIdealCharacter.primeFrobenius K L v) := by
    have h := w.agrees (integralIdealPrimeToIdeal M hM v.asIdeal v.ne_bot hv)
    exact h.trans (GaloisIdealCharacter.idealHom_prime K L w.character v)
  apply ArtinRay.galoisCharacter_eq_of_primitive_coefficients M M 1 hM hM one_ne_zero
    w.primitiveCharacter w.primitiveCharacter.inverse w.conductor_le w.conductor_le
    w.character w.character⁻¹ _ _ he
  · intro v hv _
    exact hvalue v hv
  · intro v hv _
    rw [EvenIdealRayCharacter.inverse_idealHom, hvalue v hv]
    rfl

theorem primitiveArtinZeroWitness_exists_nonreal_coefficient {s : ℂ}
    (w : PrimitiveArtinZeroWitness K L s) (hc : w.character ≠ w.character⁻¹) :
    ∃ I, (w.primitiveCharacter.coefficient I).im ≠ 0 := by
  by_contra hn
  push Not at hn
  apply primitiveArtinZeroWitness_coefficient_ne_inverse w hc
  funext I
  rw [w.primitiveCharacter.inverse_coefficient_conj]
  exact (Complex.conj_eq_iff_im.mpr (hn I)).symm

variable (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]

theorem twelfthKummer_character_pow
    (χ : Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ)
    (σ : Gal(twelfthKummerField q a/twelfthCyclotomicField q)) : (χ σ) ^ q = 1 := by
  have hcard : Nat.card Gal(twelfthKummerField q a/twelfthCyclotomicField q) ∣ q := by
    rw [IsGalois.card_aut_eq_finrank]
    exact twelfthKummerField_relative_finrank_dvd q a
  have hσ : σ ^ q = 1 := orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard σ).trans hcard)
  rw [← map_pow, hσ, map_one]

theorem twelfthKummer_nontrivial_character_ne_inverse (hq : Odd q)
    (χ : Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) (hχ : χ ≠ 1) :
    χ ≠ χ⁻¹ := by
  intro he
  apply hχ
  apply MonoidHom.ext
  intro σ
  have ht : (χ σ) ^ 2 = 1 := by
    have h := congrArg (fun θ : Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ => θ σ) he
    change χ σ = (χ σ)⁻¹ at h
    rw [pow_two]
    exact (congrArg (fun z : ℂˣ => z * χ σ) h).trans (inv_mul_cancel _)
  have hd := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr ht)
    (orderOf_dvd_iff_pow_eq_one.mpr (twelfthKummer_character_pow q a χ σ))
  rw [hq.coprime_two_left.gcd_eq_one] at hd
  change χ σ = (1 : ℂˣ)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

theorem twelfthKummer_primitive_zero_source_nonreal (hq : Odd q) {s : ℂ}
    (w : PrimitiveArtinZeroWitness (twelfthCyclotomicField q) (twelfthKummerField q a) s) :
    w.primitiveCharacter.coefficient ≠ w.primitiveCharacter.inverse.coefficient ∧
      ∃ I, (w.primitiveCharacter.coefficient I).im ≠ 0 := by
  have hc := twelfthKummer_nontrivial_character_ne_inverse q a hq w.character w.nontrivial
  exact ⟨primitiveArtinZeroWitness_coefficient_ne_inverse w hc,
    primitiveArtinZeroWitness_exists_nonreal_coefficient w hc⟩

end
end ArtinMatthews.VaryingKummerAnalytic
