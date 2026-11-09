module

public import ArtinMatthews.SourcePoissonResidueDescent
public import ArtinMatthews.SourcePoissonFinitePhase
public import ArtinMatthews.SourcePrincipalBallFrequencyTransform
public import ArtinMatthews.SourceExponentFiniteFNorm


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open VaryingKummerAnalytic SIntegerFourier SourcePhysical QuadraticWeil StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "R" => PrincipalIntegerRing T
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : SourcePrimeExponents F S₀ → R)
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourcePoissonQuotientNorm_eq (s : SourcePrimeExponents F S₀) :
    sourceQuotientNorm T (a s) = (q s : ℝ) := by
  exact congrArg (fun n : ℕ => (n : ℝ))
    (sourcePrimeExponentGenerator_quotient_card F hζ S₀ s)

theorem sourcePoissonProductGenerator_ne_zero (s A : SourcePrimeExponents F S₀) :
    a s * a A ≠ (0 : R) := by
  have h : (sourcePrimeExponentGenerator F hζ S₀ s *
      sourcePrimeExponentGenerator F hζ S₀ A : sourceRing F S₀) ≠ 0 :=
    mul_ne_zero (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s)
      (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A)
  exact h

theorem sourcePoissonQuotientFourier_eq_normalized (s A : SourcePrimeExponents F S₀) (h : R) :
    sourcePrincipalQuotientFourier F T (a s * a A)
      (sourcePoissonProductGenerator_ne_zero F S₀ hζ s A)
      (sourcePoissonNormalizedQuotientWeight F S₀ hζ s A) h =
    sourceNormalizedPeriodicFourier T (a s) (a A)
      (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s)
      (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A)
      (sourcePoissonQuotientResidue F S₀ hζ s) (sourcePoissonQuotientResidue F S₀ hζ A) h := by
  unfold sourcePrincipalQuotientFourier sourceNormalizedPeriodicFourier
  apply tsum_congr
  intro x
  have hArg : Ideal.Quotient.mk (Ideal.span {a s * a A} : Ideal R) h * x =
      Ideal.Quotient.mk _ (h * Quotient.out x) := by
    rw [map_mul, Ideal.Quotient.mk_out]
  let I : Ideal R := Ideal.span {a s * a A}
  let ψ : AddChar (R ⧸ I) ℂ := sIntegerQuotientPhase F (principalizingSet T)
    (a s * a A) (sourcePoissonProductGenerator_ne_zero F S₀ hζ s A)
  have hPhase : ψ (Ideal.Quotient.mk I h * x) = ψ (Ideal.Quotient.mk I (h * Quotient.out x)) :=
    congrArg (fun y : R ⧸ I => ψ y) hArg
  let m : R := Quotient.out x
  let G : ℂ := sourcePoissonOriginalGauss F S₀ hζ s (-m)
  have hSqrt : (Real.sqrt (sourceQuotientNorm T (a s)) : ℂ) =
      (Real.sqrt (q s : ℝ) : ℂ) :=
    congrArg (fun z : ℝ => (Real.sqrt z : ℂ)) (sourcePoissonQuotientNorm_eq F S₀ hζ s)
  have hResid := sourcePoissonQuotientResidue_mk F S₀ hζ A m
  have hWeight : sourcePoissonNormalizedQuotientWeight F S₀ hζ s A x =
      G / (Real.sqrt (sourceQuotientNorm T (a s)) : ℂ) *
        sourcePoissonQuotientResidue F S₀ hζ A (Ideal.Quotient.mk (Ideal.span {a A} : Ideal R) m) :=
    congrArg₂ (fun z r : ℂ => G / z * r) hSqrt.symm hResid.symm
  exact congrArg₂ (fun z w : ℂ => z * w) hWeight hPhase

/-- Formula (finite-Poisson-transform) on the actual (sA) quotient, including
the exact factor (sqrt{q_s}) and with no coprimality restriction. -/
theorem sourcePoissonQuotientFourier_eq_actual
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (s A : SourcePrimeExponents F S₀) (h : R) :
    sourcePrincipalQuotientFourier F T (a s * a A)
      (sourcePoissonProductGenerator_ne_zero F S₀ hζ s A)
      (sourcePoissonNormalizedQuotientWeight F S₀ hζ s A) h =
      (Real.sqrt (q s : ℝ) : ℂ) *
        sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A h := by
  refine (sourcePoissonQuotientFourier_eq_normalized F S₀ hζ s A h).trans ?_
  have he := sourceNormalizedPeriodicFourier_eq T (a s) (a A)
    (sourcePrimeExponentGenerator_ne_zero F hζ S₀ s)
    (sourcePrimeExponentGenerator_ne_zero F hζ S₀ A)
    (sourcePoissonProductPhase_primitive F S₀ hζ hBad s A)
    (sourcePoissonQuotientResidue F S₀ hζ s) (sourcePoissonQuotientResidue F S₀ hζ A) h
  refine he.trans ?_
  have hf (e : SourcePrimeExponents F S₀) :
      (fun x : R => sourcePoissonQuotientResidue F S₀ hζ e
        (Ideal.Quotient.mk (Ideal.span {a e} : Ideal R) x)) =
      reflectionExponentResidueValue F hζ S₀ e :=
    funext (sourcePoissonQuotientResidue_mk F S₀ hζ e)
  have hSqrt := congrArg (fun z : ℝ => (Real.sqrt z : ℂ))
    (sourcePoissonQuotientNorm_eq F S₀ hζ s)
  have hFinite := congrArg₂ (fun f g : R → ℂ => sourceFiniteF T (a s) (a A) h f g) (hf s) (hf A)
  exact congrArg₂ (fun z w : ℂ => z * w) hSqrt hFinite

end
end ArtinMatthews.SourceEulerAssembly
