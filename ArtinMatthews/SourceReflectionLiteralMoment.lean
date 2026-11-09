module

public import ArtinMatthews.SourceReflectionIdealMoment
public import ArtinMatthews.SourceReflectionRowClass


set_option backward.privateInPublic true
@[expose] public section

/-! Restore the actual element multiplicities and finite S-unit classes.
The only analytic inputs are the literal reflected expansion and sieve. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Rows" => SourceNonzeroFrequency F S₀
local notation "Classes" => ExteriorUnitSixthClasses (sourceHilbertSet F S₀)

theorem exists_sourceReflectionLiteralMoment_le {U : Type} [Fintype U]
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A)
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {K M ε : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (X : Finset Rows) (L : ℕ),
      (∀ m ∈ X, (q (sourceElementExponents F S₀ m.val m.property) : ℝ) ≤ K * Z ^ M) →
      (∀ e : E, (X.filter (fun m => sourceElementExponents F S₀ m.val m.property = e)).card ≤ L) →
      ∑ m ∈ X, ‖reflectionCoefficientRow F hζ S₀ hBad η m.val Z‖ ^ 2 ≤
        C * (L : ℝ) * Z ^ (2 * M - 1 + ε) := by
  let : Fintype Classes := Fintype.ofFinite _
  have hclasses (u : Classes) := exists_sourceReflectionIdealMoment_le F S₀ hζ (A u)
    hsieve hK hM hε
  choose C hC hc using hclasses
  have hC₀ : 0 ≤ ∑ u : Classes, C u := Finset.sum_nonneg (fun u _ => (hC u).le)
  refine ⟨1 + ∑ u : Classes, C u, by linarith, ?_⟩
  intro Z hZ X L hX hL
  have hz := zero_lt_one.trans_le hZ
  let ex (m : Rows) := sourceElementExponents F S₀ m.val m.property
  let cls := sourceReflectionRowClass F S₀ hζ
  let w (m : Rows) := ‖reflectionCoefficientRow F hζ S₀ hBad η m.val Z‖ ^ 2
  let v (u : Classes) (e : E) := ‖sourceReflectionIdealRow F S₀ hζ (A u) Z e‖ ^ 2
  have hweight (m : Rows) : w m = v (cls m) (ex m) := by
    dsimp only [w, v, cls, ex, sourceReflectionIdealRow]
    rw [sourceReflectionLiteralExpansion_apply F S₀ hζ η hBad A hA hz m]
  have hunit (u : Classes) :
      (∑ m ∈ X.filter (fun m => cls m = u), w m) ≤
        (L : ℝ) * C u * Z ^ (2 * M - 1 + ε) := by
    let Y := X.filter (fun m => cls m = u)
    let I := Y.image ex
    have hI (e : E) (he : e ∈ I) : (q e : ℝ) ≤ K * Z ^ M := by
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp he
      exact hX m (Finset.mem_filter.mp hm).1
    have hfiber (e : E) :
        (∑ m ∈ Y.filter (fun m => ex m = e), w m) ≤ (L : ℝ) * v u e := by
      let T := Y.filter (fun m => ex m = e)
      have hT : T.card ≤ L := by
        apply (Finset.card_le_card ?_).trans (hL e)
        intro m hm
        obtain ⟨hy, he⟩ := Finset.mem_filter.mp hm
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, he⟩
      calc
        _ = ∑ _m ∈ T, v u e := by
          apply Finset.sum_congr rfl
          intro m hm
          obtain ⟨hy, he⟩ := Finset.mem_filter.mp hm
          rw [hweight m, (Finset.mem_filter.mp hy).2, he]
        _ = (T.card : ℝ) * v u e := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hT) (sq_nonneg _)
    calc
      _ = ∑ e ∈ I, ∑ m ∈ Y.filter (fun m => ex m = e), w m :=
        (Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm) w).symm
      _ ≤ ∑ e ∈ I, (L : ℝ) * v u e := Finset.sum_le_sum (fun e _ => hfiber e)
      _ ≤ _ := by
        rw [← Finset.mul_sum, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hc u Z hZ I hI) (Nat.cast_nonneg _)
  calc
    _ = ∑ u : Classes, ∑ m ∈ X.filter (fun m => cls m = u), w m :=
      (Finset.sum_fiberwise_of_maps_to (fun u _ => Finset.mem_univ (cls u)) w).symm
    _ ≤ ∑ u : Classes, (L : ℝ) * C u * Z ^ (2 * M - 1 + ε) :=
      Finset.sum_le_sum (fun u _ => hunit u)
    _ = (∑ u : Classes, C u) * (L : ℝ) * Z ^ (2 * M - 1 + ε) := by
      rw [← Finset.sum_mul]
      simp_rw [mul_comm (L : ℝ), Finset.sum_mul]
    _ ≤ _ := by
      gcongr
      linarith

end
end ArtinMatthews.SourceEulerAssembly
