module

public import ArtinMatthews.SourceQuadraticDualRestrictedContour
public import ArtinMatthews.SourceQuadraticDualPhaseBound


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory Set QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

theorem sourceQuadraticDualRestrictedContour_norm_le (rows cols : Finset E)
    (u : E → ℂ) (g d : E) {X B σ D : ℝ} (hX : 0 < X) (hB : 1 ≤ B)
    (hσ : 0 < σ) (hσ₁ : σ < 1)
    (hamp : ∀ t : ℝ, ‖sourceQuadraticDualPairAmplitude F S₀ hζ rows cols u g d X
      (quadraticPoissonLine σ t)‖ ≤ D) :
    ‖sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B σ‖ ≤
      (∫ t : ℝ, ‖quadraticDualContourKernel F A r sourceQuadraticBlockProfile σ t‖) * D := by
  let H := quadraticDualContourKernel F A r sourceQuadraticBlockProfile σ
  have hHi := quadraticDualContourKernel_integrable F A r sourceQuadraticBlockProfile
    sourceQuadraticBlockProfile_compact sourceQuadraticBlockProfile_positive
    sourceQuadraticBlockProfile_smooth hσ (by linarith) (ne_of_lt hσ₁)
  rw [sourceQuadraticDualRestrictedContour_eq_integral F S₀ hζ rows cols u g d hX
    (zero_lt_one.trans_le hB) hσ (by linarith) (ne_of_lt hσ₁)]
  have hbound : ‖∫ t : ℝ, sourceQuadraticDualRestrictedIntegrand F S₀ hζ rows cols u g d X B σ t‖ ≤
      ∫ t : ℝ, ‖H t‖ * D := by
    apply norm_integral_le_of_norm_le (hHi.norm.mul_const D)
    filter_upwards with t
    have hpow : ‖(B : ℂ)^(-(quadraticPoissonLine σ t/2))‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hB)]
      apply Real.rpow_le_one_of_one_le_of_nonpos hB
      simp only [Complex.neg_re, Complex.div_ofNat_re, quadraticPoissonLine_re]
      linarith
    rw [sourceQuadraticDualRestrictedIntegrand, norm_mul, norm_mul]
    calc
      _ ≤ ‖H t‖ * 1 * D := mul_le_mul
        (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) (hamp t)
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  simpa only [integral_mul_const] using hbound

theorem sourceQuadraticDualRestrictedContour_interval_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) {σ : ℝ} (hσ : 0 < σ) (hσ₁ : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L K P X B : ℝ, 0 < L → 1 ≤ K → 1 ≤ P → 0 < X → 1 ≤ B →
      ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ L ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P ≤ (q b : ℝ) ∧ (q b : ℝ) ≤ 2*P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g d : E),
      ‖sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B σ‖ ≤
        C * X^(1-σ/2) * (P/(q g : ℝ))^(σ-1) *
          (K*P)^η * (2*P)^η * L^(-(σ/2)) * (P+K^α) * coeffMass cols u := by
  obtain ⟨Ca, hCa, ha⟩ := sourceQuadraticDualPairAmplitude_interval_bound F S₀ hζ htrace hE η hη
  let H := quadraticDualContourKernel F A r sourceQuadraticBlockProfile σ
  let L₀ : ℝ := 1 + ∫ t : ℝ, ‖H t‖
  have hL₀ : 0 < L₀ := by
    have hn : 0 ≤ ∫ t : ℝ, ‖H t‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [L₀]
    linarith
  refine ⟨L₀*Ca, by positivity, ?_⟩
  intro L K P X B hL hK hP hX hB rows cols hrows hcols hclass u g d
  let D := Ca * X^(1-σ/2) * (P/(q g : ℝ))^(σ-1) *
    (K*P)^η * (2*P)^η * L^(-(σ/2)) * (P+K^α) * coeffMass cols u
  have hmass : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hamp (t : ℝ) : ‖sourceQuadraticDualPairAmplitude F S₀ hζ rows cols u g d X
      (quadraticPoissonLine σ t)‖ ≤ D := by
    simpa only [quadraticPoissonLine_re] using
      ha L K P X hL hK hP hX rows cols hrows hcols hclass u g d
        (quadraticPoissonLine σ t) (by rw [quadraticPoissonLine_re]; exact hσ.le)
        (by rw [quadraticPoissonLine_re]; exact hσ₁.le)
  calc
    _ ≤ (∫ t : ℝ, ‖H t‖) * D :=
      sourceQuadraticDualRestrictedContour_norm_le F S₀ hζ rows cols u g d hX hB hσ hσ₁ hamp
    _ ≤ L₀*D := mul_le_mul_of_nonneg_right (by dsimp [L₀]; linarith) hD
    _ = _ := by dsimp [D]; ring

end
end ArtinMatthews.SourceEulerAssembly
