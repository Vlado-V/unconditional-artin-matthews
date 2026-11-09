module

public import ArtinMatthews.SourceQuadraticCutoffPairEstimate
public import ArtinMatthews.QuadraticHeckeCutoffWeightBounds


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "D" => HeckeIdealMobius.divisors F

/-- The finite main-term sum with its original cutoff weights and bounded column twists. -/
def sourceQuadraticCutoffMainSum (g : Ideal (𝓞 F)) (rows cols : Finset E)
    (weight : Ideal (𝓞 F) → Ideal (𝓞 F) → E → ℂ)
    (twist : Ideal (𝓞 F) → Ideal (𝓞 F) → E → ℂ) (coeff : E → ℂ) : ℂ :=
  ∑ d ∈ D g, ∑ e ∈ D g, ∑ h ∈ rows,
    weight d e h * sourceQuadraticCutoffPairValue F S₀ hζ cols h
      (fun b => coeff b * twist d e b)

private theorem sqrt_cutoff_shape {M H : ℝ} (hM : 0 ≤ M) (hH : 0 < H)
    (P α : ℝ) :
    Real.sqrt M * (1 / Real.sqrt H) * (P + H ^ α) =
      Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P := by
  rw [Real.rpow_sub hH, ← Real.sqrt_eq_rpow, Real.sqrt_div hM]
  ring

variable [IsTotallyComplex F]

/-- The retained squarefree row cutoff gives the GL7.3 bound. -/
theorem sourceQuadraticCutoffMainSum_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M P H : ℝ), 1 ≤ M → 1 ≤ P → 1 ≤ H → H ≤ M →
      ∀ (g : Ideal (𝓞 F)), Squarefree g → ∀ (rows cols : Finset E),
      (∀ h ∈ rows, sourceReflectionIsSquarefree h ∧ (q h : ℝ) ≤ H) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ P) →
      ∀ (weight : Ideal (𝓞 F) → Ideal (𝓞 F) → E → ℂ)
        (twist : Ideal (𝓞 F) → Ideal (𝓞 F) → E → ℂ) (coeff : E → ℂ),
      (∀ d ∈ D g, ∀ e ∈ D g, ∀ h ∈ rows, ‖weight d e h‖ ≤ 1 / Real.sqrt H) →
      (∀ d ∈ D g, ∀ e ∈ D g, ∀ b ∈ cols, ‖twist d e b‖ ≤ 1) →
      ‖(Real.sqrt M : ℂ) * sourceQuadraticCutoffMainSum F S₀ hζ g rows cols weight twist coeff‖ ≤
        C * (Ideal.absNorm g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by
  obtain ⟨C, hC, hpair⟩ := sourceQuadraticCutoffPair_of_exponent F S₀ hζ htrace hE ε hε
  refine ⟨C, hC, ?_⟩
  intro M P H hM hP hH hHM g hg rows cols hrows hcols weight twist coeff hweight htwist
  let mass := ∑ b ∈ cols, ‖coeff b‖ ^ 2
  let B := C * (H * P) ^ ε * (P + H ^ α) * mass
  have hH0 := zero_lt_one.trans_le hH
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (d : Ideal (𝓞 F)) (hd : d ∈ D g) (e : Ideal (𝓞 F)) (he : e ∈ D g) :
      ‖∑ h ∈ rows, weight d e h * sourceQuadraticCutoffPairValue F S₀ hζ cols h
        (fun b => coeff b * twist d e b)‖ ≤ (1 / Real.sqrt H) * B := by
    have hmassTwist : (∑ b ∈ cols, ‖coeff b * twist d e b‖ ^ 2) ≤ mass := by
      apply Finset.sum_le_sum
      intro b hb
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (htwist d hd e he b hb)
    have hp := hpair H P hH hP rows cols hrows hcols (fun b => coeff b * twist d e b)
    have hp' : (∑ h ∈ rows, ‖sourceQuadraticCutoffPairValue F S₀ hζ cols h
        (fun b => coeff b * twist d e b)‖) ≤ B :=
      hp.trans (mul_le_mul_of_nonneg_left hmassTwist (by positivity))
    calc
      _ ≤ ∑ h ∈ rows, ‖weight d e h * sourceQuadraticCutoffPairValue F S₀ hζ cols h
          (fun b => coeff b * twist d e b)‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ rows, (1 / Real.sqrt H) * ‖sourceQuadraticCutoffPairValue F S₀ hζ cols h
          (fun b => coeff b * twist d e b)‖ := by
        apply Finset.sum_le_sum
        intro h hh
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hweight d hd e he h hh) (norm_nonneg _)
      _ = (1 / Real.sqrt H) * ∑ h ∈ rows, ‖sourceQuadraticCutoffPairValue F S₀ hζ cols h
          (fun b => coeff b * twist d e b)‖ := (Finset.mul_sum ..).symm
      _ ≤ (1 / Real.sqrt H) * B := mul_le_mul_of_nonneg_left hp' (by positivity)
  have hsum : ‖sourceQuadraticCutoffMainSum F S₀ hζ g rows cols weight twist coeff‖ ≤
      ((D g).card : ℝ) ^ 2 * ((1 / Real.sqrt H) * B) := by
    unfold sourceQuadraticCutoffMainSum
    calc
      _ ≤ ∑ d ∈ D g, ‖∑ e ∈ D g, ∑ h ∈ rows, weight d e h *
          sourceQuadraticCutoffPairValue F S₀ hζ cols h (fun b => coeff b * twist d e b)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ d ∈ D g, ∑ e ∈ D g, (1 / Real.sqrt H) * B := by
        apply Finset.sum_le_sum
        intro d hd
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e he => hterm d hd e he))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two]; ring
  have hg1 : (1 : ℝ) ≤ Ideal.absNorm g := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hg.ne_zero)
  have hcard : ((D g).card : ℝ) ^ 2 ≤ (Ideal.absNorm g : ℝ) ^ 4 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (by exact_mod_cast quadraticHecke_divisor_card_le_norm F g hg) 2).trans
      (pow_le_pow_right₀ hg1 (by norm_num : (2 : ℕ) ≤ 4))
  have hpowers : (H * P) ^ ε ≤ (M * P) ^ ε :=
    Real.rpow_le_rpow (mul_nonneg hH0.le hP0.le) (mul_le_mul_of_nonneg_right hHM hP0.le) hε.le
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg M)]
  calc
    _ ≤ Real.sqrt M * (((D g).card : ℝ) ^ 2 * ((1 / Real.sqrt H) * B)) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt M * ((Ideal.absNorm g : ℝ) ^ 4 * ((1 / Real.sqrt H) * B)) := by
      gcongr
    _ = C * (Ideal.absNorm g : ℝ) ^ 4 * (H * P) ^ ε *
        (Real.sqrt M * (1 / Real.sqrt H) * (P + H ^ α)) * mass := by dsimp [B]; ring
    _ ≤ C * (Ideal.absNorm g : ℝ) ^ 4 * (M * P) ^ ε *
        (Real.sqrt M * (1 / Real.sqrt H) * (P + H ^ α)) * mass := by
      gcongr
    _ = _ := by rw [sqrt_cutoff_shape hM0.le hH0]

end
end ArtinMatthews.SourceEulerAssembly
