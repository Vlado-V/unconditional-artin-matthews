module

public import ArtinMatthews.SourceKPResidualUnitInitial
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPCuspNativeTraceSlice


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen Filter
open scoped NumberField AdeleRing MatrixGroups Topology BigOperators NNReal ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "V" => InfinitePlace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

/-- The two fixed box tests share a literal period and density. The
common archimedean value is canceled at the residue parameter. -/
theorem sourceKPCuspResidualCoefficient_unit_translate_of_measure
    (m : Kˣ) (qf : Gf) (d : 𝓞 K) (hd : d ≠ 0)
    (hpm : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (hp1 : sourceKPCuspNativeFinitePeriod K hζ d (sourceKPCuspResidualUnitTranslate K hζ m qf))
    (hm : ∃ r : 𝓞 K, (m:K)*(d:K) = (r:K)) (c : ℝ≥0) (hc : 0 < c)
    (hmap : Measure.map (sourceKPCuspProductCoordinates K hζ d hd).symm (productVolume V) =
      (c:ℝ≥0∞) • (volume : Measure (I → ℝ)).prod (sourceKPCuspProductHeightMeasure K))
    {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspResidualCoefficient K hζ d hd (sourceKPCuspResidualUnitTranslate K hζ m qf) 1 c hT =
      sourceKPCuspResidualFrequencyScale K hζ m (1/6)*sourceKPCuspResidualCoefficient K hζ d hd qf m c hT := by
  let Q := sourceKPCuspResidualUnitTranslate K hζ m qf
  let B := sourceKPCuspHeightBox K
  let hB := sourceKPCuspHeightBox_isCompact K
  let hpos := sourceKPCuspHeightBox_positive K
  let Fm := sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos (m:K) hT
  let F1 := sourceKPCuspNativeFourierTest K hζ d hd Q B hB hpos (1:K) hT
  let Mm := sourceKPCuspArchFourierMoment K hζ m B
  let M1 := sourceKPCuspArchFourierMoment K hζ (1:Kˣ) B
  let A := sourceKPCuspResidualUnitArchValue K hζ
  let L := sourceKPCuspResidualFrequencyScale K hζ m
  let U : Set ℂ := {s | 0 < s.re}
  let z₀ : ℂ := 1/6
  have hz₀ : z₀ ∈ U := by change 0 < (1/6:ℂ).re; norm_num
  have hU : IsPreconnected U :=
    ((convex_Ioi (𝕜 := ℝ) (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hm1 : ∃ r : 𝓞 K, ((1:Kˣ):K)*(d:K) = (r:K) := ⟨d,by simp⟩
  have hFm : MeromorphicOn Fm U :=
    sourceKPCuspNativeFourierTest_meromorphic K hζ d hd qf B hB hpos (m:K) hT
  have hF1 : MeromorphicOn F1 U :=
    sourceKPCuspNativeFourierTest_meromorphic K hζ d hd Q B hB hpos (1:K) hT
  have hMm : AnalyticOnNhd ℂ Mm U :=
    sourceKPCuspArchFourierMoment_analyticOnNhd K hζ d hd m B hB hpos
  have hM1 : AnalyticOnNhd ℂ M1 U :=
    sourceKPCuspArchFourierMoment_analyticOnNhd K hζ d hd 1 B hB hpos
  have hA : AnalyticOnNhd ℂ A U := sourceKPCuspResidualUnitArchValue_analyticOnNhd K hζ
  have hL : AnalyticOnNhd ℂ L U := fun s _ => sourceKPCuspResidualFrequencyScale_analyticAt K hζ m s
  have hLeft : MeromorphicOn (fun s => Fm s*M1 s*A s*L s) U := fun s hs =>
    (((hFm s hs).mul (hM1 s hs).meromorphicAt).mul (hA s hs).meromorphicAt).mul (hL s hs).meromorphicAt
  have hRight : MeromorphicOn (fun s => F1 s*Mm s*A s) U := fun s hs =>
    ((hF1 s hs).mul (hMm s hs).meromorphicAt).mul (hA s hs).meromorphicAt
  have hInitial (s : ℂ) (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
      Fm s*M1 s*A s*L s = F1 s*Mm s*A s := by
    let Jm := ∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K
    let J1 := ∫ z, sourceKPTraceJacquetFiniteKernel K hζ 1 s Q z ∂sourceKPFiniteStandardHaar K
    have hmF : Fm s = (c:ℂ)*Mm s*Jm :=
      sourceKPCuspNativeFourierTest_initial_factor_of_measure K hζ d hd qf hpm
        B hB hpos m hm c hc hmap T hT s hs
    have h1F : F1 s = (c:ℂ)*M1 s*J1 :=
      sourceKPCuspNativeFourierTest_initial_factor_of_measure K hζ d hd Q hp1
        B hB hpos 1 hm1 c hc hmap T hT s hs
    have hJ : A s*L s*Jm = A s*J1 := sourceKPCuspResidualUnit_initial K hζ m qf hs
    rw [hmF,h1F]
    calc
      _ = ((c:ℂ)*Mm s*M1 s)*(A s*L s*Jm) := by ring
      _ = ((c:ℂ)*Mm s*M1 s)*(A s*J1) := by rw [hJ]
      _ = _ := by ring
  let b : ℝ := ((3*(Module.finrank ℚ K+1):ℕ):ℝ)
  let a : ℂ := b
  have hb : 0 < b := by dsimp only [b]; positivity
  have ha : a ∈ U := by change 0 < a.re; simpa only [a,Complex.ofReal_re] using hb
  have hab : b/2 < a.re := by simp only [a,Complex.ofReal_re]; linarith
  have he : (fun s => Fm s*M1 s*A s*L s) =ᶠ[𝓝 a] (fun s => F1 s*Mm s*A s) := by
    filter_upwards [(Complex.continuous_re.tendsto a).eventually (Ioi_mem_nhds hab)] with s hs
    apply hInitial
    change b ≤ 2*s.re+1
    linarith
  have heq := sourceKPMeromorphicOn_eventuallyEq_of_germ hLeft hRight hU ha hz₀ he
  let Rm := sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos (m:K) hT
  let R1 := sourceKPCuspNativeFourierResidue K hζ d hd Q B hB hpos (1:K) hT
  have hmLim : Tendsto (fun s => (s-z₀)*Fm s) (𝓝[≠] z₀) (𝓝 Rm) :=
    sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd qf B hB hpos (m:K) hT
  have h1Lim : Tendsto (fun s => (s-z₀)*F1 s) (𝓝[≠] z₀) (𝓝 R1) :=
    sourceKPCuspNativeFourierTest_residue_tendsto K hζ d hd Q B hB hpos (1:K) hT
  have hMmLim : Tendsto Mm (𝓝[≠] z₀) (𝓝 (Mm z₀)) :=
    (hMm z₀ hz₀).continuousAt.mono_left nhdsWithin_le_nhds
  have hM1Lim : Tendsto M1 (𝓝[≠] z₀) (𝓝 (M1 z₀)) :=
    (hM1 z₀ hz₀).continuousAt.mono_left nhdsWithin_le_nhds
  have hALim : Tendsto A (𝓝[≠] z₀) (𝓝 (A z₀)) :=
    (hA z₀ hz₀).continuousAt.mono_left nhdsWithin_le_nhds
  have hLLim : Tendsto L (𝓝[≠] z₀) (𝓝 (L z₀)) :=
    (hL z₀ hz₀).continuousAt.mono_left nhdsWithin_le_nhds
  have hres : Rm*M1 z₀*A z₀*L z₀ = R1*Mm z₀*A z₀ := by
    apply tendsto_nhds_unique (((hmLim.mul hM1Lim).mul hALim).mul hLLim)
    apply ((h1Lim.mul hMmLim).mul hALim).congr'
    filter_upwards [heq] with s hs
    simpa only [mul_assoc] using congrArg (fun w : ℂ => (s-z₀)*w) hs.symm
  have hc₀ : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hMm₀ : Mm z₀ ≠ 0 := sourceKPCuspArchFourierMoment_oneSixth_ne_zero K hζ m
  have hM1₀ : M1 z₀ ≠ 0 := sourceKPCuspArchFourierMoment_oneSixth_ne_zero K hζ 1
  have hA₀ : A z₀ ≠ 0 := sourceKPCuspResidualUnitArchValue_oneSixth_ne_zero K hζ
  change R1/((c:ℂ)*M1 z₀) = L z₀*(Rm/((c:ℂ)*Mm z₀))
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hc₀ hM1₀) (mul_ne_zero hMm₀ hA₀))
  calc
    _ = R1*Mm z₀*A z₀ := by field_simp [hc₀,hM1₀] <;> ring
    _ = Rm*M1 z₀*A z₀*L z₀ := hres.symm
    _ = _ := by field_simp [hc₀,hMm₀] <;> ring

theorem sourceKPCuspResidualFourierValue_unit_translate (m : Kˣ) (qf : Gf)
    {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCuspResidualFourierValue K hζ 1 hT (sourceKPCuspResidualUnitTranslate K hζ m qf) =
      sourceKPCuspResidualFrequencyScale K hζ m (1/6)*sourceKPCuspResidualFourierValue K hζ m hT qf := by
  let Q := sourceKPCuspResidualUnitTranslate K hζ m qf
  let g : Bool → SourceKPAdelicProjective K hζ
    | false => (1,qf)
    | true => (1,Q)
  obtain ⟨d,hd,hm,hp⟩ := sourceKPAdelicCuspFrequencyPeriod_common K hζ (m:K) g
  have hpm : sourceKPCuspNativeFinitePeriod K hζ d qf := hp false
  have hp1 : sourceKPCuspNativeFinitePeriod K hζ d Q := hp true
  have hm1 : ∃ r : 𝓞 K, ((1:Kˣ):K)*(d:K) = (r:K) := ⟨d,by simp⟩
  obtain ⟨c,hc,hmap⟩ := sourceKPCuspProductCoordinates_map_productVolume K hζ d hd
  change sourceKPCuspResidualFourierValue K hζ 1 hT Q = _
  rw [sourceKPCuspResidualFourierValue_eq_coefficient K hζ 1 hT Q d hd c hc hp1 hm1 hmap,
    sourceKPCuspResidualFourierValue_eq_coefficient K hζ m hT qf d hd c hc hpm hm hmap]
  exact sourceKPCuspResidualCoefficient_unit_translate_of_measure K hζ m qf d hd hpm hp1 hm c hc hmap hT

end
end ArtinMatthews
