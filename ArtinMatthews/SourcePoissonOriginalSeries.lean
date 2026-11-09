module

public import ArtinMatthews.SourcePoissonOriginalProbe


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open VaryingKummerAnalytic SIntegerFourier SourcePhysical StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "R" => PrincipalIntegerRing T
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : SourcePrimeExponents F S₀ → R)
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "C" => ReflectionSquarefreeExponents F S₀
local notation "E" => SourcePrimeExponents F S₀

theorem sourcePoissonOriginalGauss_norm_le (e : E) (m : R) :
    ‖sourcePoissonOriginalGauss F S₀ hζ e m‖ ≤ (q e : ℝ) := by
  let I : Ideal R := Ideal.span {a e}
  let : Finite (R ⧸ I) := sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e
  let : Fintype (R ⧸ I) := Fintype.ofFinite _
  have hc : Fintype.card (R ⧸ I) = q e :=
    (Nat.card_eq_fintype_card).symm.trans (sourcePrimeExponentGenerator_quotient_card F hζ S₀ e)
  let ψ : AddChar (R ⧸ I) ℂ := sIntegerQuotientPhase F S (a e) (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e)
  change ‖∑' d : R ⧸ I, sourcePoissonQuotientResidue F S₀ hζ e d *
    ψ (Ideal.Quotient.mk I m * d)‖ ≤ (q e : ℝ)
  rw [tsum_fintype, ← hc]
  calc
    _ ≤ ∑ d : R ⧸ I, ‖sourcePoissonQuotientResidue F S₀ hζ e d *
        ψ (Ideal.Quotient.mk I m * d)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : R ⧸ I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      have hp : ‖ψ (Ideal.Quotient.mk I m * d)‖ = 1 :=
        AddChar.norm_apply ψ (Ideal.Quotient.mk I m * d)
      have hr : ‖sourcePoissonQuotientResidue F S₀ hζ e d‖ ≤ 1 :=
        reflectionExponentResidueValue_norm_le_one F hζ S₀ e (Quotient.out d)
      calc
        _ = ‖sourcePoissonQuotientResidue F S₀ hζ e d‖ := by rw [norm_mul, hp, mul_one]
        _ ≤ 1 := hr
    _ = _ := by simp

theorem sourcePoissonOriginalGauss_test_summable_norm (e : E) (t : SNormOne F S) (V : ℝ)
    (hTest : Summable (fun m : R => ‖sourcePoissonOriginalTest F S₀ hζ t V m‖)) :
    Summable (fun m : R =>
      ‖(sourcePoissonOriginalGauss F S₀ hζ e (-m) / (Real.sqrt (q e : ℝ) : ℂ)) *
        sourcePoissonOriginalTest F S₀ hζ t V m‖) := by
  have hq : 0 < (q e : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ e)
  let b : ℝ := (q e : ℝ) / Real.sqrt (q e : ℝ)
  have hNonneg (m : R) :
      0 ≤ ‖(sourcePoissonOriginalGauss F S₀ hζ e (-m) / (Real.sqrt (q e : ℝ) : ℂ)) *
        sourcePoissonOriginalTest F S₀ hζ t V m‖ := norm_nonneg _
  refine Summable.of_nonneg_of_le hNonneg ?_ (hTest.mul_left b)
  intro m
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (sourcePoissonOriginalGauss_norm_le F S₀ hζ e (-m))
      (Real.sqrt_pos.mpr hq).le) (norm_nonneg _)

private theorem sourcePoissonReflectionCoefficientMajorant_summable (Z : ℝ) :
    Summable (fun p : C × E =>
      (Real.exp (2 ^ 2 : ℝ) / (2 * Real.sqrt Real.pi)) * Z ^ (2 : ℝ) *
        ((q p.1.val : ℝ) ^ (-2 : ℝ) * (q p.2 : ℝ) ^ (-2 : ℝ))) := by
  have hn := sourcePrimeExponentNorm_summable F S₀ (σ := 2) (by norm_num)
  have hc : Summable (fun c : C => (q c.val : ℝ) ^ (-2 : ℝ)) :=
    hn.subtype (fun e => ∀ P, e P ≤ 1)
  exact (summable_mul_of_summable_norm hc.norm hn.norm).mul_left _

private theorem sourcePoissonCoefficient_interchange {I P : Type}
    (g : I → ℂ) (hg : Summable (fun m => ‖g m‖))
    (f : I → P → ℂ) (B : P → ℝ) (hB : Summable B) (hle : ∀ m p, ‖f m p‖ ≤ B p) :
    (∑' m, g m * (∑' p, f m p)) = ∑' p, ∑' m, g m * f m p := by
  have hA (x : I × P) : ‖g x.1 * f x.1 x.2‖ ≤ ‖g x.1‖ * B x.2 := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hle x.1 x.2) (norm_nonneg (g x.1))
  have hProd : Summable (fun x : I × P => ‖g x.1‖ * B x.2) :=
    summable_mul_of_summable_norm hg.norm hB.norm
  have h0 (x : I × P) : 0 ≤ ‖g x.1 * f x.1 x.2‖ := norm_nonneg _
  have hSumNorm : Summable (fun x : I × P => ‖g x.1 * f x.1 x.2‖) :=
    Summable.of_nonneg_of_le h0 hA hProd
  have hSum : Summable (fun x : I × P => g x.1 * f x.1 x.2) := hSumNorm.of_norm
  have hExpand (m : I) : g m * (∑' p : P, f m p) = ∑' p : P, g m * f m p := by
    rw [tsum_mul_left]
  have hSwap : (∑' m : I, ∑' p : P, g m * f m p) = ∑' p : P, ∑' m : I, g m * f m p :=
    hSum.tsum_comm.symm
  exact (tsum_congr hExpand).trans hSwap

variable [IsTotallyComplex F]
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- Absolute convergence justifies expanding the original coefficient row before
Poisson summation, without dropping the original squarefree condition. -/
theorem sourcePoissonOriginalCoefficient_expand
    (hBad : standardWeilBadPlaces F ⊆ S) {Z : ℝ} (hZ : 0 < Z)
    (g : R → ℂ) (hg : Summable (fun m => ‖g m‖)) :
    (∑' m : R, g m * reflectionCoefficientRow F hζ S₀ hBad η m Z) =
      ∑' p : C × E, ∑' m : R,
        g m * reflectionCoefficientTerm F hζ S₀ hBad η p.1 p.2 m Z := by
  let B (p : C × E) :=
    (Real.exp (2 ^ 2 : ℝ) / (2 * Real.sqrt Real.pi)) * Z ^ (2 : ℝ) *
      ((q p.1.val : ℝ) ^ (-2 : ℝ) * (q p.2 : ℝ) ^ (-2 : ℝ))
  let f (m : R) (p : C × E) := reflectionCoefficientTerm F hζ S₀ hBad η p.1 p.2 m Z
  have hB : Summable B := sourcePoissonReflectionCoefficientMajorant_summable F S₀ Z
  have hLe (m : R) (p : C × E) : ‖f m p‖ ≤ B p :=
    reflectionCoefficientTerm_dedekind_majorant F hζ S₀ hBad η p.1 p.2 m hZ
  have hRow (m : R) : reflectionCoefficientRow F hζ S₀ hBad η m Z = ∑' p, f m p :=
    reflectionCoefficientRow_eq_product_tsum F hζ S₀ hBad η m hZ
  simp_rw [hRow]
  exact sourcePoissonCoefficient_interchange g hg f B hB hLe

end
end ArtinMatthews.SourceEulerAssembly
