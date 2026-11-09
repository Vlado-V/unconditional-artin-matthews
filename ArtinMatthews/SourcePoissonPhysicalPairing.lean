module

public import ArtinMatthews.SourcePoissonPrimalAbsolute
public import ArtinMatthews.SourcePoissonOriginalSupport


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "E" => SourcePrimeExponents F S₀

/-- The fixed-scale additive coefficient of one literal exterior ideal. -/
def sourcePoissonPhysicalAdditiveTerm (X Y : ℝ) (t : SNormOne F S) (s : E) (m : R) : ℂ :=
  sourceProbeW1Complex ((q s : ℝ) / Y) * (Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹ *
    ((sourcePoissonOriginalGauss F S₀ hζ s (-m) / (Real.sqrt (q s : ℝ) : ℂ)) *
      sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m)

/-- The actual physical additive factor paired with the reflection coefficients. -/
def sourcePoissonPhysicalAdditiveFactor (X Y : ℝ) (t : SNormOne F S) (m : R) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : E, sourcePoissonPhysicalAdditiveTerm F S₀ hζ X Y t s m

theorem sourcePoissonPhysicalAdditiveTerm_summable_norm
    (X Y : ℝ) (t : SNormOne F S) (s : E) :
    Summable (fun m : R => ‖sourcePoissonPhysicalAdditiveTerm F S₀ hζ X Y t s m‖) := by
  let K := sourceProbeW1Complex ((q s : ℝ) / Y) * (Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹
  have h := sourcePoissonOriginalGauss_test_summable_norm F S₀ hζ s t ((q s : ℝ) * X)
    (sourcePoissonOriginalTest_summable_norm F S₀ hζ t ((q s : ℝ) * X))
  exact (h.mul_left ‖K‖).congr (fun _ => (norm_mul _ _).symm)

variable [IsTotallyComplex F] {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- Uniform in the original lattice point for each fixed Gaussian scale. -/
theorem sourcePoissonReflectionCoefficientRow_uniform
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {Z : ℝ} (hZ : 0 < Z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : R, ‖reflectionCoefficientRow F hζ S₀ hBad η m Z‖ ≤ B := by
  let C := ReflectionSquarefreeExponents F S₀
  let B (p : C × E) :=
    (Real.exp (2 ^ 2 : ℝ) / (2 * Real.sqrt Real.pi)) * Z ^ (2 : ℝ) *
      ((q p.1.val : ℝ) ^ (-2 : ℝ) * (q p.2 : ℝ) ^ (-2 : ℝ))
  have hn := sourcePrimeExponentNorm_summable F S₀ (σ := 2) (by norm_num)
  have hc : Summable (fun c : C => (q c.val : ℝ) ^ (-2 : ℝ)) :=
    hn.subtype (fun e => ∀ P, e P ≤ 1)
  have hB : Summable B := (summable_mul_of_summable_norm hc.norm hn.norm).mul_left _
  have hB0 (p : C × E) : 0 ≤ B p := by
    dsimp only [B]
    positivity
  refine ⟨∑' p, B p, tsum_nonneg hB0, fun m => ?_⟩
  have hS := reflectionCoefficientRow_summable_norm F hζ S₀ hBad η m hZ
  have hle (p : C × E) : ‖reflectionCoefficientTerm F hζ S₀ hBad η p.1 p.2 m Z‖ ≤ B p :=
    reflectionCoefficientTerm_dedekind_majorant F hζ S₀ hBad η p.1 p.2 m hZ
  rw [reflectionCoefficientRow_eq_product_tsum F hζ S₀ hBad η m hZ]
  exact (norm_tsum_le_tsum_norm hS).trans (hS.tsum_le_tsum hle hB)

/-- The original probe density is the exact physical pairing before applying
Cauchy–Schwarz. The s-sum is finite by the actual support of W1. -/
theorem sourcePoissonOriginalDensity_eq_additivePairing
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X : ℝ) {Y Z : ℝ} (hY : 0 < Y) (hZ : 0 < Z) (t : SNormOne F S) :
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t =
      ∑' m : R, sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m *
        reflectionCoefficientRow F hζ S₀ hBad η m Z := by
  let P := (sourcePoissonOriginalCompactWeight_finite F S₀ hY).toFinset
  let B (m : R) := reflectionCoefficientRow F hζ S₀ hBad η m Z
  let A (s : E) := sourcePoissonPhysicalAdditiveTerm F S₀ hζ X Y t s
  let W (s : E) := sourceProbeW1Complex ((q s : ℝ) / Y)
  have hW (s : E) (hs : s ∉ P) : W s = 0 := by
    by_contra hw
    exact hs (((sourcePoissonOriginalCompactWeight_finite F S₀ hY).mem_toFinset).mpr hw)
  have hAz (s : E) (hs : s ∉ P) (m : R) : A s m = 0 := by
    change W s * _ * _ = 0
    rw [hW s hs, zero_mul, zero_mul]
  have hS (s : E) : Summable (fun m : R => A s m * B m) := by
    obtain ⟨K, hK, hKB⟩ := sourcePoissonReflectionCoefficientRow_uniform F S₀ hζ η hBad hZ
    have hA := sourcePoissonPhysicalAdditiveTerm_summable_norm F S₀ hζ X Y t s
    have hn (m : R) : 0 ≤ ‖A s m * B m‖ := norm_nonneg _
    have hb (m : R) : ‖A s m * B m‖ ≤ ‖A s m‖ * K := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hKB m) (norm_nonneg _)
    exact (Summable.of_nonneg_of_le hn hb (hA.mul_right K)).of_norm
  have hDensity :
      sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t =
        (Y : ℂ)⁻¹ * ∑' s : E, ∑' m : R, A s m * B m := by
    unfold sourcePoissonOriginalDensity
    apply congrArg (fun z : ℂ => (Y : ℂ)⁻¹ * z)
    apply tsum_congr
    intro s
    rw [show (∑' m : R, A s m * B m) =
        (W s * (Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹) *
        ∑' m : R, (sourcePoissonOriginalGauss F S₀ hζ s (-m) /
          (Real.sqrt (q s : ℝ) : ℂ)) *
          sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m * B m by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      dsimp only [A, W, sourcePoissonPhysicalAdditiveTerm]
      ac_rfl]
    rw [mul_assoc]
  rw [hDensity, tsum_eq_sum (s := P)]
  · rw [← Summable.tsum_finsetSum (fun s _ => hS s), ← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [sourcePoissonPhysicalAdditiveFactor, tsum_eq_sum (s := P)]
    · change (Y : ℂ)⁻¹ * (∑ s ∈ P, A s m * B m) =
        ((Y : ℂ)⁻¹ * (∑ s ∈ P, A s m)) * B m
      rw [mul_assoc, Finset.sum_mul]
    · exact fun s hs => hAz s hs m
  · intro s hs
    simp only [hAz s hs, zero_mul, tsum_zero]

end
end ArtinMatthews.SourceEulerAssembly
