module

public import ArtinMatthews.SourceKPSelectedCuspMoment
public import ArtinMatthews.SourceKPCuspOutgoingFactor
public import ArtinMatthews.SourceKPCuspBandUnfolding


set_option backward.privateInPublic true
@[expose] public section

/-! The selected full-dimensional cusp-band functional extracts one actual outgoing coefficient. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "HY" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "HC" => sourceKPAdelicCoverHeight K hζ
local notation "HF" => sourceKPFiniteLevelHeight K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPSelectedCuspWeight_memLp (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) : MemLp (sourceKPSelectedCuspWeight K hζ b A B) 2 μY :=
  sourceKPAutomorphicBandWeight_memLp K hζ _ (sourceKPSelectedCuspWeight_measurable K hζ b A B)
    (sourceKPSelectedCuspWeight_norm_le K hζ b A B)
    (fun y hy => (sourceKPSelectedCuspWeight_support K hζ b hA hy).2)

def sourceKPSelectedCuspBandPairing (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ} (hA : 1 ≤ A) :
    SourceKPGenuineAutomorphicL2 K hζ →L[ℂ] ℂ :=
  sourceKPGenuineAutomorphicL2Pairing K hζ (sourceKPSelectedCuspWeight K hζ b A B)
    (sourceKPSelectedCuspWeight_memLp K hζ b hA)

theorem sourceKPSelectedCuspBandPairing_eq_intertwiner
    (qf : SourceKPFiniteAdeleProjective K hζ) {T A B : ℝ} (hT : 1 ≤ T) (hTA : 2*T ≤ A)
    (hA : 1 ≤ A) {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (u : SourceKPGenuineAutomorphicL2 K hζ)
    (hu : (u.val : Y → ℂ) =ᵐ[μY] sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :
    sourceKPSelectedCuspBandPairing K hζ (sourceKPFiniteLevelMk K hζ (1,qf)).2 (B := B) hA u =
      sourceKPAdelicTraceIntertwiner K hζ s (1,qf) *
        sourceKPSelectedCuspMoment K hζ (sourceKPFiniteLevelMk K hζ (1,qf)).2 A B
          (HC (1,qf)) s := by
  let b := (sourceKPFiniteLevelMk K hζ (1,qf)).2
  let S := sourceKPSelectedCuspBand K hζ b A B
  let h := HC (1,qf)
  let W := sourceKPSelectedCuspWeight K hζ b A B
  let R := sourceKPSelectedCuspRadialValue K hζ h s
  let G : Y → ℂ := S.indicator R
  let m := sourceKPAdelicTraceIntertwiner K hζ s (1,qf)
  let proj := sourceKPHighCuspProjection K hζ A
  let π := sourceKPAutomorphicCompactMk K hζ
  let F := sourceKPCuspBandHighSection K hζ A
  have hh : 0 < h := sourceKPAdelicCoverHeight_pos K hζ _
  have hSm : MeasurableSet S := (sourceKPSelectedCuspBand_isOpen K hζ b A B).measurableSet
  have hGm : Measurable G := (sourceKPSelectedCuspRadialValue_measurable K hζ h s).indicator hSm
  have hGI : Integrable G μY := (integrable_indicator_iff hSm).mpr
    (sourceKPSelectedCuspRadialValue_integrableOn K hζ b hA hh s)
  have hlow {y : Y} (hy : HY y ≤ A) : y ∉ S := by
    intro hyS
    exact (not_lt.mpr hy) (sourceKPSelectedCuspBand_height K hζ b hA hyS).1
  have hW0 (y : Y) (hy : HY y ≤ A) : W y = 0 := Set.indicator_of_notMem (hlow hy) _
  have hG0 (y : Y) (hy : HY y ≤ A) : G y = 0 := Set.indicator_of_notMem (hlow hy) _
  have hbig : (3 : ℝ) ≤ ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ 3*(Module.finrank ℚ K+1))
  have hs' : 0 < s.re := by linarith
  have hpair := sourceKPCuspBandPairing_eq_outgoing K hζ hT hTA W
    (sourceKPSelectedCuspWeight_memLp K hζ b hA) hW0
    (fun q y hq => sourceKPSelectedCuspWeight_upper K hζ b (B := B) hA q hq y) hs u hu
  have hpoint (x : SourceKPHighCuspFinite K hζ A) :
      star (W (π (proj x).val))*sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val =
        m*G (π (proj x).val) := by
    let y := sourceKPFiniteLevelToCompact K hζ x.val
    change star (W y)*sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val = m*G y
    by_cases hy : y ∈ S
    · have hhigh : 1 < HF x.val := hA.trans_lt x.property
      have hOrbit : x.val.2 ∈ Set.range (fun γ : sourceKPRationalBorel K => γ.val • b) := by
        obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ x.val
        have hqH : 1 < HC q := by rwa [← hq,sourceKPFiniteLevelHeight_mk] at hhigh
        have hy' : sourceKPFiniteLevelToCompact K hζ (sourceKPFiniteLevelMk K hζ q) ∈ S :=
          (congrArg (sourceKPFiniteLevelToCompact K hζ) hq).symm ▸ hy
        exact (congrArg Prod.snd hq) ▸ ((sourceKPSelectedCuspBand_mem_iff K hζ b hA q hqH).mp hy').2.2
      have hW : W y = 1 := Set.indicator_of_mem hy _
      have hG : G y = R y := Set.indicator_of_mem hy _
      rw [hW,star_one,one_mul,hG,
        sourceKPFiniteLevelOutgoingEisenstein_eq_height_ratio K hζ hs' qf x.val hOrbit]
      have hheight : HY y = HF x.val := sourceKPFiniteLevelToCompact_height_of_high K hζ x.val hhigh
      have hp : 0 < HF x.val/h := div_pos (sourceKPFiniteLevelHeight_pos K hζ _) hh
      change m*((HF x.val/h : ℝ) : ℂ)^((1/2 : ℂ)-s) = m*R y
      congr 1
      change ((HF x.val/h : ℝ) : ℂ)^((1/2 : ℂ)-s) =
        Complex.exp (((1/2 : ℂ)-s)*(Real.log (HY y/h) : ℂ))
      rw [hheight,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
        ← Complex.ofReal_log hp.le,mul_comm]
    · have hW : W y = 0 := Set.indicator_of_notMem hy _
      have hG : G y = 0 := Set.indicator_of_notMem hy _
      rw [hW,hG,star_zero,zero_mul,mul_zero]
  have hsec := sourceKPCuspBandHighSection_measurePreserving K hζ A
  have hf : Measurable (fun x : SourceKPHighCuspAutomorphic K hζ A => G (π x.val)) :=
    hGm.comp ((sourceKPAutomorphicCompactMk_measurable K hζ).comp measurable_subtype_coe)
  have hmoment : (∫ x in F, G (π (proj x).val) ∂sourceKPHighRepresentativeHaar K hζ A) =
      sourceKPSelectedCuspMoment K hζ b A B h s := by
    calc
      _ = ∫ x : SourceKPHighCuspAutomorphic K hζ A, G (π x.val) ∂sourceKPHighCuspMeasure K hζ A := by
        have hm : AEStronglyMeasurable (fun x : SourceKPHighCuspAutomorphic K hζ A => G (π x.val))
            (Measure.map proj (Measure.restrict (sourceKPHighRepresentativeHaar K hζ A) F)) :=
          hsec.map_eq.symm ▸ hf.aestronglyMeasurable
        have he := integral_map hsec.measurable.aemeasurable hm
        rw [hsec.map_eq] at he
        exact he.symm
      _ = ∫ y, G y ∂μY := (sourceKPAutomorphicBandIntegral_eq_high K hζ G hGI A hG0).symm
      _ = _ := integral_indicator hSm
  change sourceKPGenuineAutomorphicL2Pairing K hζ W _ u = m*_
  rw [hpair]
  trans ∫ x in F, m*G (π (proj x).val) ∂sourceKPHighRepresentativeHaar K hζ A
  · exact setIntegral_congr_fun (sourceKPCuspBandHighSection_spec K hζ A).1 (fun x _ => hpoint x)
  · rw [integral_const_mul,hmoment]

end
end ArtinMatthews
