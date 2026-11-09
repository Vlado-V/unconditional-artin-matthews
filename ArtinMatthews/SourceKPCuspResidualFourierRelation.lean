module

public import ArtinMatthews.SourceKPResidualTranslateRepresentative
public import ArtinMatthews.SourceKPCuspResidualFourierValue


set_option backward.privateInPublic true
@[expose] public section

/-! The compact Fourier functional vanishes on literal common-level
relations among the translated residual vectors. -/
namespace ArtinMatthews

open NumberField Matrix MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing BigOperators NNReal ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V

theorem sourceKPCuspResidualFourierValue_sum_eq_zero_of_translateCombination
    (F : Finset Gf) {ι : Type*} [Fintype ι] (t : ι → Gf)
    (ht : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i))
    (a : ι → ℂ) {T : ℝ} (hT : 2 < T)
    (hz : sourceKPResidualTranslateCombination K hζ F t ht a hT = 0)
    (m : Kˣ) (qf : Gf) :
    (∑ i, a i * sourceKPCuspResidualFourierValue K hζ m (show 1 ≤ T by linarith) (qf*t i)) = 0 := by
  classical
  obtain ⟨d,hd,hm,hp⟩ := sourceKPAdelicCuspFrequencyPeriod_common K hζ (m:K)
    (fun i : ι => ((1,qf*t i) : SourceKPAdelicProjective K hζ))
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  have hT' : 1 ≤ T := by linarith
  let B := sourceKPCuspHeightBox K
  let hB := sourceKPCuspHeightBox_isCompact K
  let hbpos := sourceKPCuspHeightBox_positive K
  let S := sourceKPCuspNativeBand K hζ d hd B
  let R (i : ι) (p : X) := (sourceKPAutomorphicExceptionalResidue K hζ hT').val
    (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk (qf*t i)) p)
  let φ (p : X) := star (sourceKPCuspNativeFrequency K hζ d hd (m:K) p)
  let f (i : ι) (p : X) := φ p * R i p
  let den := (c:ℂ)*sourceKPCuspArchFourierMoment K hζ m B (1/6)
  have hint (i : ι) : IntegrableOn (f i) S (productVolume V) :=
    sourceKPCuspNativeFourierResidue_band_integrable K hζ d hd (qf*t i)
      B hB hbpos (m:K) hT'
  have hcoe (i : ι) :
      sourceKPCuspResidualFourierValue K hζ m hT' (qf*t i) =
        (∫ p in S, f i p ∂productVolume V) / den := by
    rw [sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT' (qf*t i) d hd c hc
      (hp i) hm hmap]
    change sourceKPCuspNativeFourierResidue K hζ d hd (qf*t i) B hB hbpos (m:K) hT' / den =
      (∫ p in S, f i p ∂productVolume V) / den
    rw [sourceKPCuspNativeFourierResidue_band_integral K hζ d hd (qf*t i)
      B hB hbpos (m:K) hT']
  have hAE : ∀ᵐ p ∂(productVolume V).restrict S, (∑ i, a i * R i p) = 0 :=
    ae_restrict_of_ae (sourceKPResidualTranslateCombination_native_zero K hζ F t ht a hT hz qf)
  have hsum : (∑ i, a i * (∫ p in S, f i p ∂productVolume V)) = 0 := by
    calc
      _ = ∫ p in S, ∑ i, a i * f i p ∂productVolume V := by
        rw [integral_finsetSum Finset.univ (fun i _ => (hint i).const_mul (a i))]
        simp only [integral_const_mul]
      _ = ∫ p in S, (0:ℂ) ∂productVolume V := by
        apply integral_congr_ae
        filter_upwards [hAE] with p hp
        calc
          _ = φ p * (∑ i, a i * R i p) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by dsimp only [f]; ring)
          _ = 0 := by rw [hp, mul_zero]
      _ = 0 := by rw [integral_zero]
  change (∑ i, a i * sourceKPCuspResidualFourierValue K hζ m hT' (qf*t i)) = 0
  simp_rw [hcoe, ← mul_div_assoc]
  rw [← Finset.sum_div, hsum, zero_div]

end
end ArtinMatthews
