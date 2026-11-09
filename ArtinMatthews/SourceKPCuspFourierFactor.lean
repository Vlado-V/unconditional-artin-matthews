module

public import ArtinMatthews.SourceKPCuspNativeFourierTest
public import ArtinMatthews.SourceKPCuspNativeFourierCoefficient
public import ArtinMatthews.SourceKPCuspHeightJacquetProfile


set_option backward.privateInPublic true
@[expose] public section

/-! Exact full-dimensional Fourier testing in a principal cusp band.
The finite integral remains the literal coupled adelic section. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups Topology ENNReal NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

private theorem nativeCellTest_eq_of_band (m : K) (B : Set (V → ℝ)) (p : X)
    (hp : p ∈ sourceKPCuspNativeBand K hζ d hd B) :
    sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p =
      sourceKPCuspNativeFrequency K hζ d hd m p := by
  rw [sourceKPCuspNativeCellTest,if_pos hp.1,star_one,mul_one]

private theorem nativeCellTest_eq_zero_off_band (m : K) (B : Set (V → ℝ)) (p : X)
    (hp : p ∈ sourceKPCuspNativeCompactBox K hζ d hd B)
    (hn : p ∉ sourceKPCuspNativeBand K hζ d hd B) :
    sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p = 0 := by
  apply if_neg
  intro hcell
  apply hn
  exact ⟨hcell,((sourceKPCuspNativeCompactBox_mem K hζ d hd B p).mp hp).2⟩

theorem sourceKPCuspNativeFourierTest_initial_band
    (qf : SourceKPFiniteAdeleProjective K hζ) (B : Set (V → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K)
    {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos m hT s =
      ∫ p in sourceKPCuspNativeBand K hζ d hd B,
        star (sourceKPCuspNativeFrequency K hζ d hd m p) *
          sourceKPAutomorphicCompactEisenstein K hζ s
            (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p)
        ∂productVolume V := by
  rw [sourceKPCuspNativeFourierTest_initial K hζ d hd qf B hB hpos m hT hs]
  let F := fun p : X => star (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p) *
    sourceKPAutomorphicCompactEisenstein K hζ s
      (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p)
  calc
    _ = ∫ p in sourceKPCuspNativeBand K hζ d hd B, F p ∂productVolume V := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB).measurableSet.nullMeasurableSet
        (sourceKPCuspNativeBand_subset_compactBox K hζ d hd B)
      filter_upwards with p hp
      rw [nativeCellTest_eq_zero_off_band K hζ d hd m B p hp.1 hp.2,star_zero,zero_mul]
    _ = _ := by
      apply setIntegral_congr_fun (sourceKPCuspNativeBand_measurable K hζ d hd B hB.measurableSet)
      intro p hp
      dsimp only [F]
      rw [nativeCellTest_eq_of_band K hζ d hd m B p hp]

theorem sourceKPCuspNativeFourierTest_band_integrable
    (qf : SourceKPFiniteAdeleProjective K hζ) (B : Set (V → ℝ))
    (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K)
    {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    IntegrableOn (fun p : X => star (sourceKPCuspNativeFrequency K hζ d hd m p) *
      sourceKPAutomorphicCompactEisenstein K hζ s
        (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p))
      (sourceKPCuspNativeBand K hζ d hd B) (productVolume V) := by
  have hi := (sourceKPCuspNativeFourierTest_integrableOn K hζ d hd qf B hB hpos m hT hs).mono_set
    (sourceKPCuspNativeBand_subset_compactBox K hζ d hd B)
  apply hi.congr
  filter_upwards [ae_restrict_mem (sourceKPCuspNativeBand_measurable K hζ d hd B hB.measurableSet)] with p hp
  rw [nativeCellTest_eq_of_band K hζ d hd m B p hp]

def sourceKPCuspArchFourierMoment (m : Kˣ) (B : Set (V → ℝ)) (s : ℂ) : ℂ :=
  ∫ y in B, sourceKPTraceJacquetArchProfile K hζ m s y ∂sourceKPCuspProductHeightMeasure K

theorem sourceKPCuspNativeFourierTest_initial_factor_of_measure
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
          sourceKPFiniteDeepCoverLift K hζ k)
    (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
    (m : Kˣ) (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K))
    (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (E).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K)) :
    ∀ (T : ℝ) (hT : 1 ≤ T) (s : ℂ),
      ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 →
      sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos (m:K) hT s =
        (c:ℂ) * sourceKPCuspArchFourierMoment K hζ m B s *
          ∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K := by
  intro T hT s hs
  have hspos : 0 < s.re := by
    have hdeg : 0 ≤ (Module.finrank ℚ K:ℝ) := Nat.cast_nonneg _
    push_cast at hs
    linarith
  rw [sourceKPCuspNativeFourierTest_initial_band K hζ d hd qf B hB hpos (m:K) hT hs]
  rw [sourceKPCuspNativeBand_integral K hζ d hd c hc hmap B hB.measurableSet _
    (sourceKPCuspNativeFourierTest_band_integrable K hζ d hd qf B hB hpos (m:K) hT hs)]
  have he : (∫ y in B, ∫ x : I → ℝ,
      star (sourceKPCuspNativeFrequency K hζ d hd (m:K) (E (x,y))) *
        sourceKPAutomorphicCompactEisenstein K hζ s
          (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) (E (x,y)))
      ∂unitTorusUnitCellMeasure I ∂sourceKPCuspProductHeightMeasure K) =
      sourceKPCuspArchFourierMoment K hζ m B s *
        ∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K := by
    calc
      _ = ∫ y in B, sourceKPTraceJacquetArchProfile K hζ m s y *
          (∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K)
          ∂sourceKPCuspProductHeightMeasure K := by
        apply setIntegral_congr_fun hB.measurableSet
        intro y hy
        simp_rw [sourceKPCuspNativeFrequency_coordinates]
        rw [sourceKPCuspNativeEisenstein_fourier K hζ d hd qf hperiod hs m hm y (hpos y hy),
          sourceKPCuspHeightSection_arch_jacquet K hζ hspos m y (hpos y hy)]
      _ = _ := by rw [integral_mul_const]; rfl
  rw [he,mul_assoc]

theorem sourceKPCuspNativeFourierTest_initial_factor
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        (1,qf)⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * (1,qf) =
          sourceKPFiniteDeepCoverLift K hζ k)
    (m : Kˣ) (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K)) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (B : Set (V → ℝ)) (hB : IsCompact B) (hpos : ∀ y ∈ B, ∀ v, 0 < y v)
        (T : ℝ) (hT : 1 ≤ T) (s : ℂ),
        ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1 →
        sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos (m:K) hT s =
          (c:ℂ) * sourceKPCuspArchFourierMoment K hζ m B s *
            ∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K := by
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  exact ⟨c,hc,fun B hB hpos T hT s hs =>
    sourceKPCuspNativeFourierTest_initial_factor_of_measure K hζ d hd qf hperiod
      B hB hpos m hm c hc hmap T hT s hs⟩

end
end ArtinMatthews
