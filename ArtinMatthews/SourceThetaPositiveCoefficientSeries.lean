module

public import ArtinMatthews.SourceThetaPositiveSheetBounds
public import ArtinMatthews.ReflectionCoefficientBeforeGaussian


set_option backward.privateInPublic true
@[expose] public section

/-! The literal exterior positive-sheet series before Gaussian smoothing.
The two ideal coordinates retain their actual common primes. -/

namespace ArtinMatthews.SourceReflection

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable (hS : QuadraticWeil.standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
variable {M : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K M)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (c : InfinitePlace K → ℝ)
variable (U : ∀ p : S, SourceThetaFiniteCutoff K p.val) (v : InfinitePlace K)

local notation "E" => SourcePrimeExponents K S₀
local notation "C" => ReflectionSquarefreeExponents K S₀
local notation "H" => sourceThetaPositiveSheet K S c U hζ v

def sourceThetaPositiveCoefficientTerm (b : C) (n : E) (row : sourceRing K S₀) (T : ℝ) : ℂ :=
  reflectionCoefficientBeforeGaussian K hζ S₀ hS η b n row *
    H ((sourcePrimeExponentNorm K S₀ (b.val + 3 • n) : ℝ) * T)

def sourceThetaPositiveCoefficientSeries (row : sourceRing K S₀) (T : ℝ) : ℂ :=
  ∑' b : C, ∑' n : E, sourceThetaPositiveCoefficientTerm K hζ S₀ hS η S c U v b n row T

theorem sourceThetaPositiveCoefficientSeries_summable_norm (hc : ∀ w, 0 < c w)
    (row : sourceRing K S₀) {T : ℝ} (hT : 0 < T) :
    Summable (fun p : C × E =>
      ‖sourceThetaPositiveCoefficientTerm K hζ S₀ hS η S c U v p.1 p.2 row T‖) := by
  obtain ⟨B, hB, hH⟩ := sourceThetaPositiveSheet_norm_bound K S c hc U hζ v 2 (by norm_num)
  have hD := reflectionCoefficientBeforeGaussian_dirichlet_summable K hζ S₀ hS η row
    (σ := 2) (by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hD.mul_left (B * T ^ (-2 : ℝ)))
  intro p
  let N : ℝ := sourcePrimeExponentNorm K S₀ (p.1.val + 3 • p.2)
  have hN : 0 < N := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos K S₀ _)
  let a := reflectionCoefficientBeforeGaussian K hζ S₀ hS η p.1 p.2 row
  change ‖a * H (N * T)‖ ≤ (B * T ^ (-2 : ℝ)) * (‖a‖ * N ^ (-2 : ℝ))
  rw [norm_mul]
  calc
    _ ≤ ‖a‖ * (B * (N * T) ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hH _ (mul_pos hN hT)) (norm_nonneg _)
    _ = _ := by rw [Real.mul_rpow hN.le hT.le]; ac_rfl

theorem sourceThetaPositiveCoefficientSeries_eq_product_tsum (hc : ∀ w, 0 < c w)
    (row : sourceRing K S₀) {T : ℝ} (hT : 0 < T) :
    sourceThetaPositiveCoefficientSeries K hζ S₀ hS η S c U v row T =
      ∑' p : C × E, sourceThetaPositiveCoefficientTerm K hζ S₀ hS η S c U v p.1 p.2 row T :=
  (sourceThetaPositiveCoefficientSeries_summable_norm K hζ S₀ hS η S c U v hc row hT).of_norm.tsum_prod.symm

end
end ArtinMatthews.SourceReflection
