module

public import ArtinMatthews.SourcePoissonOriginalProbe
public import ArtinMatthews.SourceGeneratorPrefix
public import ArtinMatthews.SourceKernelTableBridge


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open VaryingKummerAnalytic SIntegerFourier SourceCRTNormalization StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "R" => PrincipalIntegerRing T
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : SourcePrimeExponents F S₀ → R)

theorem sourcePoissonResidueValue_congr
    (e : SourcePrimeExponents F S₀) {x y : R}
    (hxy : Ideal.Quotient.mk (Ideal.span {a e} : Ideal R) x = Ideal.Quotient.mk _ y) :
    reflectionExponentResidueValue F hζ S₀ e x =
      reflectionExponentResidueValue F hζ S₀ e y := by
  unfold reflectionExponentResidueValue sourcePrimeExponentWeight Finsupp.prod
  apply Finset.prod_congr rfl
  intro P hP
  have hd : sourceAllowedPrimeGenerator F hζ S₀ P ^ e P ∣ a e := by
    unfold sourcePrimeExponentGenerator Finsupp.prod
    exact Finset.dvd_prod_of_mem
      (fun j : SourceExteriorPrime F S₀ => sourceAllowedPrimeGenerator F hζ S₀ j ^ e j) hP
  let p : R := sourceAllowedPrimeGenerator F hζ S₀ P
  let I : Ideal R := Ideal.span {(a e : R)}
  let J : Ideal R := primePowerIdeal T P.val (e P)
  have hJ : J = Ideal.span {p ^ e P} := by
    have h := sourceDegreeIdealEq T P.val p (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) (e P)
    simpa only [sourceDegreeGenerator_eq_pow T p (e P)] using h
  have hle : I ≤ Ideal.span {p ^ e P} :=
    Ideal.span_singleton_le_span_singleton.mpr hd
  let π : (R ⧸ I) →+* (R ⧸ J) := Ideal.Quotient.factor (hJ.symm ▸ hle)
  have he : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y :=
    congrArg π hxy
  change sourceLocalPowerWeight T P.val P.property p (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
      (reflectionPrimeCharacters F hζ S₀ P) (e P) (Ideal.Quotient.mk J x) =
    sourceLocalPowerWeight T P.val P.property p (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
      (reflectionPrimeCharacters F hζ S₀ P) (e P) (Ideal.Quotient.mk J y)
  rw [he]

@[simp] theorem sourcePoissonQuotientResidue_mk (e : SourcePrimeExponents F S₀) (x : R) :
    sourcePoissonQuotientResidue F S₀ hζ e (Ideal.Quotient.mk _ x) =
      reflectionExponentResidueValue F hζ S₀ e x :=
  sourcePoissonResidueValue_congr F S₀ hζ e (Ideal.Quotient.mk_out _)

theorem sourcePoissonOriginalGauss_congr (e : SourcePrimeExponents F S₀) {x y : R}
    (hxy : Ideal.Quotient.mk (Ideal.span {a e} : Ideal R) x = Ideal.Quotient.mk _ y) :
    sourcePoissonOriginalGauss F S₀ hζ e x = sourcePoissonOriginalGauss F S₀ hζ e y := by
  let I : Ideal (PrincipalIntegerRing (sourceHilbertSeed F S₀)) := Ideal.span {a e}
  have hxy' : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := hxy
  let f (z : PrincipalIntegerRing (sourceHilbertSeed F S₀) ⧸ I) :=
    sourcePoissonQuotientResidue F S₀ hζ e z
  let ψ := sIntegerQuotientPhase F (sourceHilbertSet F S₀) (a e)
    (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e)
  change (∑' d, f d * ψ (Ideal.Quotient.mk I x * d)) =
    ∑' d, f d * ψ (Ideal.Quotient.mk I y * d)
  rw [hxy']

/-- The original product (q_s^{-1/2}g_s(-m)\chi_A(m)) is a function of the
literal quotient by (sA). -/
def sourcePoissonNormalizedQuotientWeight (s A : SourcePrimeExponents F S₀)
    (x : R ⧸ Ideal.span {a s * a A}) : ℂ :=
  (sourcePoissonOriginalGauss F S₀ hζ s (-Quotient.out x) /
    (Real.sqrt (sourcePrimeExponentNorm F S₀ s : ℝ) : ℂ)) *
    reflectionExponentResidueValue F hζ S₀ A (Quotient.out x)

theorem sourcePoissonNormalizedQuotientWeight_mk
    (s A : SourcePrimeExponents F S₀) (x : R) :
    sourcePoissonNormalizedQuotientWeight F S₀ hζ s A
      (Ideal.Quotient.mk (Ideal.span {a s * a A} : Ideal R) x) =
      (sourcePoissonOriginalGauss F S₀ hζ s (-x) /
        (Real.sqrt (sourcePrimeExponentNorm F S₀ s : ℝ) : ℂ)) *
        reflectionExponentResidueValue F hζ S₀ A x := by
  have hs : Ideal.span {a s * a A} ≤ Ideal.span {a s} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
  have hA : Ideal.span {a s * a A} ≤ Ideal.span {a A} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)
  have hx : Ideal.Quotient.mk (Ideal.span {a s * a A} : Ideal R)
      (Quotient.out (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x :=
    Ideal.Quotient.mk_out _
  have hxs := congrArg (Ideal.Quotient.factor hs) hx
  have hxA := congrArg (Ideal.Quotient.factor hA) hx
  change Ideal.Quotient.mk (Ideal.span {a s} : Ideal R) (Quotient.out (Ideal.Quotient.mk
    (Ideal.span {a s * a A} : Ideal R) x)) = Ideal.Quotient.mk _ x at hxs
  change Ideal.Quotient.mk (Ideal.span {a A} : Ideal R) (Quotient.out (Ideal.Quotient.mk
    (Ideal.span {a s * a A} : Ideal R) x)) = Ideal.Quotient.mk _ x at hxA
  have hxsn : Ideal.Quotient.mk (Ideal.span {a s} : Ideal R) (-Quotient.out (Ideal.Quotient.mk
      (Ideal.span {a s * a A} : Ideal R) x)) = Ideal.Quotient.mk _ (-x) := by
    simpa only [map_neg] using congrArg Neg.neg hxs
  exact congrArg₂ (fun g r : ℂ =>
    g / (Real.sqrt (sourcePrimeExponentNorm F S₀ s : ℝ) : ℂ) * r)
      (sourcePoissonOriginalGauss_congr F S₀ hζ s hxsn)
      (sourcePoissonResidueValue_congr F S₀ hζ A hxA)

end
end ArtinMatthews.SourceEulerAssembly
