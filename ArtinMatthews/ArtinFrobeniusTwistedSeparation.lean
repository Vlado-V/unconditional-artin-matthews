module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealConductorOne
public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ArtinMatthews.ArtinFrobeniusPrimeAvoidance
public import ArtinMatthews.IdealRayCoefficientSeparation
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

/-! Fixed twists cancel at actual Artin primes outside all old moduli.
This proves both coefficient separation and uniqueness of a principal
twisted row without assigning any value at a bad prime. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain GaloisIdealCharacter
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem galoisCharacter_eq_of_twisted_good_prime_values
    (M₁ M₂ C : Ideal (𝓞 K)) (hM₁ : M₁ ≠ ⊥) (hM₂ : M₂ ≠ ⊥) (hC : C ≠ ⊥)
    (α : FractionalIdealGroup K →* ℂˣ) (χ θ : Gal(L/K) →* ℂˣ)
    (he : ∀ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M₁ →
      IsCoprime v.asIdeal M₂ → IsCoprime v.asIdeal C →
      α (integralIdealFractionalUnit v.asIdeal v.ne_bot) * (χ (primeFrobenius K L v))⁻¹ =
      α (integralIdealFractionalUnit v.asIdeal v.ne_bot) * (θ (primeFrobenius K L v))⁻¹) :
    χ = θ := by
  by_contra hne
  obtain ⟨v,hv,hsep⟩ := exists_prime_separating_frobenius_avoiding
    (M₁*M₂*C) (mul_ne_zero (mul_ne_zero hM₁ hM₂) hC) χ θ hne
  have hc : (IsCoprime v.asIdeal M₁ ∧ IsCoprime v.asIdeal M₂) ∧
      IsCoprime v.asIdeal C := by simpa only [IsCoprime.mul_right_iff] using hv
  exact hsep (inv_injective (mul_left_cancel (he v hc.1.1 hc.1.2 hc.2)))

theorem galoisCharacter_eq_of_twisted_coefficients
    (M₁ M₂ C : Ideal (𝓞 K)) (hM₁ : M₁ ≠ ⊥) (hM₂ : M₂ ≠ ⊥) (hC : C ≠ ⊥)
    {f g : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K f) (φ : EvenIdealRayCharacter K g)
    (hf : M₁ ≤ f) (hg : M₂ ≤ g)
    (α : FractionalIdealGroup K →* ℂˣ) (χ θ : Gal(L/K) →* ℂˣ)
    (hψ : ∀ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M₁ → IsCoprime v.asIdeal C →
      ψ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) =
      α (integralIdealFractionalUnit v.asIdeal v.ne_bot) * (χ (primeFrobenius K L v))⁻¹)
    (hφ : ∀ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M₂ → IsCoprime v.asIdeal C →
      φ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) =
      α (integralIdealFractionalUnit v.asIdeal v.ne_bot) * (θ (primeFrobenius K L v))⁻¹)
    (he : ψ.coefficient = φ.coefficient) : χ = θ := by
  apply galoisCharacter_eq_of_twisted_good_prime_values M₁ M₂ C hM₁ hM₂ hC α χ θ
  intro v h₁ h₂ hC
  have hcf := h₁.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hf)
  have hcg := h₂.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hg)
  exact (hψ v h₁ hC).symm.trans
    ((EvenIdealRayCharacter.idealHom_eq_of_coefficient_eq_of_coprime ψ φ he
      v.asIdeal v.ne_bot hcf hcg).trans (hφ v h₂ hC))

theorem galoisCharacter_eq_of_principal_twists
    (M₁ M₂ C : Ideal (𝓞 K)) (hM₁ : M₁ ≠ ⊥) (hM₂ : M₂ ≠ ⊥) (hC : C ≠ ⊥)
    {f g : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K f) (φ : EvenIdealRayCharacter K g)
    (hf : M₁ ≤ f) (hg : M₂ ≤ g)
    (α : FractionalIdealGroup K →* ℂˣ) (χ θ : Gal(L/K) →* ℂˣ)
    (hψ : ∀ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M₁ → IsCoprime v.asIdeal C →
      ψ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) =
      α (integralIdealFractionalUnit v.asIdeal v.ne_bot) * (χ (primeFrobenius K L v))⁻¹)
    (hφ : ∀ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M₂ → IsCoprime v.asIdeal C →
      φ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) =
      α (integralIdealFractionalUnit v.asIdeal v.ne_bot) * (θ (primeFrobenius K L v))⁻¹)
    (hpψ : ¬ψ.IsNonprincipal) (hpφ : ¬φ.IsNonprincipal) : χ = θ := by
  apply galoisCharacter_eq_of_twisted_good_prime_values M₁ M₂ C hM₁ hM₂ hC α χ θ
  intro v h₁ h₂ hC
  have hcf := h₁.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hf)
  have hcg := h₂.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hg)
  have hvalψ : ψ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) = 1 := by
    by_contra h
    exact hpψ ⟨v.asIdeal,v.ne_bot,hcf,h⟩
  have hvalφ : φ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) = 1 := by
    by_contra h
    exact hpφ ⟨v.asIdeal,v.ne_bot,hcg,h⟩
  exact (hψ v h₁ hC).symm.trans (hvalψ.trans (hvalφ.symm.trans (hφ v h₂ hC)))

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
