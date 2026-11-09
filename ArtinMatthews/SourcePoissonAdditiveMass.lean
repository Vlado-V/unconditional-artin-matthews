module

public import ArtinMatthews.SourcePoissonOriginalSeries
public import ArtinMatthews.SourceReducedFractionLabels
public import ArtinMatthews.NumberFieldIdealLinearCount


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical SIntegerPrincipalization
open VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "OS" => PrincipalIntegerRing (sourceHilbertSeed F S₀)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : E → OS)
local notation "U" e => (OS ⧸ (Ideal.span {a e} : Ideal OS))ˣ

/-- All units in each literal exterior quotient are finite, with count at most its norm. -/
@[instance_reducible] def sourcePoissonQuotientUnitFintype (e : E) : Fintype (U e) := by
  let : Finite (OS ⧸ (Ideal.span {a e} : Ideal OS)) :=
    sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e
  exact Fintype.ofFinite _

theorem sourcePoissonQuotientUnit_card_le (e : E) :
    Nat.card (U e) ≤ q e := by
  let I : Ideal OS := Ideal.span {a e}
  let : Finite (OS ⧸ I) := sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e
  calc
    Nat.card (U e) ≤ Nat.card (OS ⧸ I) :=
      Nat.card_le_card_of_injective (fun d : U e => (d : OS ⧸ I)) Units.val_injective
    _ = q e := sourcePrimeExponentGenerator_quotient_card F hζ S₀ e

/-- Linear count of the actual exterior denominator exponents in the fixed norm window. -/
theorem exists_sourcePoissonSupportedExponent_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ) (P : Finset E), 1 ≤ Y →
      (∀ e ∈ P, (q e : ℝ) ≤ (5 / 2 : ℝ) * Y) → (P.card : ℝ) ≤ C * Y := by
  obtain ⟨C, hC, hb⟩ := exists_idealNormCount_linear F
  refine ⟨C * (7 / 2), by positivity, ?_⟩
  intro Y P hY hP
  let N := ⌈(5 / 2 : ℝ) * Y⌉₊
  have hNpos : 1 ≤ N := Nat.succ_le_of_lt (Nat.ceil_pos.mpr (by positivity))
  have hN : (N : ℝ) ≤ (7 / 2 : ℝ) * Y :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (5 / 2 : ℝ) * Y)).le.trans (by linarith)
  let f (e : P) : {I : Ideal (𝓞 F) // I.absNorm ≤ N} :=
    ⟨sourcePrimeExponentIdeal F S₀ e.val, by
      rw [sourcePrimeExponentIdeal_norm]
      exact_mod_cast (hP e.val e.property).trans (Nat.le_ceil _)⟩
  let : Finite {I : Ideal (𝓞 F) // I.absNorm ≤ N} :=
    Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N
  have hf : Function.Injective f := by
    intro e e' h
    exact Subtype.ext (sourcePrimeExponentIdeal_injective F S₀ (congrArg Subtype.val h))
  have hcard : P.card ≤ idealNormCount F N := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, idealNormCount] using
      Nat.card_le_card_of_injective f hf
  calc
    (P.card : ℝ) ≤ (idealNormCount F N : ℝ) := by exact_mod_cast hcard
    _ ≤ C * N := hb N hNpos
    _ ≤ C * ((7 / 2 : ℝ) * Y) := mul_le_mul_of_nonneg_left hN hC.le
    _ = _ := by ring

/-- The actual quotient-unit mass before the outer factor of the separated mode. -/
theorem sourcePoissonQuotientUnit_mass (e : E) (Y : ℝ) (hY : 0 < Y)
    (w : ℂ) (hw : ‖w‖ ≤ 1) :
    letI := sourcePoissonQuotientUnitFintype F S₀ hζ e
    (∑ d : U e, ‖(Y : ℂ)⁻¹ *
      (sourcePoissonQuotientResidue F S₀ hζ e d.val / (Real.sqrt (q e : ℝ) : ℂ)) * w‖ ^ 2) ≤
      (Y ^ 2)⁻¹ := by
  let := sourcePoissonQuotientUnitFintype F S₀ hζ e
  have hq : 0 < (q e : ℝ) := by exact_mod_cast sourcePrimeExponentNorm_pos F S₀ e
  have hs : 0 < Real.sqrt (q e : ℝ) := Real.sqrt_pos.mpr hq
  have hc : (Fintype.card (U e) : ℝ) ≤ q e := by
    exact_mod_cast (Nat.card_eq_fintype_card (α := U e)).symm.le.trans
      (sourcePoissonQuotientUnit_card_le F S₀ hζ e)
  have hterm (d : U e) : ‖(Y : ℂ)⁻¹ *
      (sourcePoissonQuotientResidue F S₀ hζ e d.val / (Real.sqrt (q e : ℝ) : ℂ)) * w‖ ≤
        Y⁻¹ * (Real.sqrt (q e : ℝ))⁻¹ := by
    have hd : ‖sourcePoissonQuotientResidue F S₀ hζ e d.val‖ ≤ 1 :=
      reflectionExponentResidueValue_norm_le_one F hζ S₀ e (Quotient.out d.val)
    rw [norm_mul, norm_mul, norm_inv, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hY.le, Real.norm_of_nonneg hs.le]
    calc
      _ ≤ Y⁻¹ * (‖sourcePoissonQuotientResidue F S₀ hζ e d.val‖ / Real.sqrt (q e : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ Y⁻¹ * (1 / Real.sqrt (q e : ℝ)) * 1 := by
        gcongr
      _ = _ := by simp
  have hsq : (Y⁻¹ * (Real.sqrt (q e : ℝ))⁻¹) ^ 2 = (Y ^ 2)⁻¹ * (q e : ℝ)⁻¹ := by
    rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt hq.le]
  calc
    _ ≤ ∑ _ : U e, (Y ^ 2)⁻¹ * (q e : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d _
      rw [← hsq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hterm d) 2
    _ = (Fintype.card (U e) : ℝ) * ((Y ^ 2)⁻¹ * (q e : ℝ)⁻¹) := by simp
    _ ≤ (q e : ℝ) * ((Y ^ 2)⁻¹ * (q e : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by field_simp

end
end ArtinMatthews.SourceEulerAssembly
