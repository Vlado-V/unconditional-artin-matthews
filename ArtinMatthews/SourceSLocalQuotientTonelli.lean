module

public import ArtinMatthews.SourceSLocalQuotientOrbit


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "μ" => sourceSLocalProbeQuotientMeasure K hζ S v
local notation "D" => sNormOneFundamentalSet K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "N" => SNormOne K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "f" => sourceSLocalProbeScaled K hζ S v
local notation "g" => sourceSLocalProbeOrbitTranslate K hζ S v
local notation "P" => sourceSLocalProbeOrbit K hζ S v

def sourceSLocalProbeAbsoluteMass (c : ℂ) (u : SWholeUnits K S) : ℝ≥0∞ :=
  ∫⁻ x : N, ‖c * f u x‖ₑ ∂ν

theorem sourceSLocalProbeAbsoluteMass_eq_real (c : ℂ) (u : SWholeUnits K S) :
    sourceSLocalProbeAbsoluteMass K hζ S v c u =
      ENNReal.ofReal (‖c‖ * ∫ x : N, ‖f u x‖ ∂ν) := by
  have h : Integrable (fun x : N => c * f u x) ν :=
    (sourceSLocalProbeSheetScaled_integrable K hζ S v u).const_mul c
  unfold sourceSLocalProbeAbsoluteMass
  rw [← ofReal_integral_norm_eq_lintegral_enorm h]
  simp_rw [norm_mul]
  rw [integral_const_mul]

/-- The absolute mass is controlled before any complex sum or integral is exchanged. -/
theorem sourceSLocalProbeAbsoluteMass_le (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℂ) (u : SWholeUnits K S),
      sourceSLocalProbeAbsoluteMass K hζ S v c u ≤
        ENNReal.ofReal (‖c‖ * (C * sLocalNorm K S u ^ (-σ))) := by
  obtain ⟨C, hC, hB⟩ := sourceSLocalProbeSheetScaled_integral_norm_le K hζ S v σ hσ
  refine ⟨C, hC, fun c u => ?_⟩
  rw [sourceSLocalProbeAbsoluteMass_eq_real]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB u) (norm_nonneg c))

/-- Tonelli on the actual fundamental set for the distinct sixth-power translates. -/
theorem sourceSLocalProbeOrbit_absoluteMass (c : ℂ) (u : SWholeUnits K S) :
    (∫⁻ x in D, ∑' a : Γ, ‖c * g u a x‖ₑ ∂ν) =
      sourceSLocalProbeAbsoluteMass K hζ S v c u := by
  let : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  rw [lintegral_tsum fun a =>
    ((sourceSLocalProbeOrbitTranslate_measurable K hζ S v u a).const_mul c).enorm.aemeasurable]
  calc
    _ = ∑' a : (Γ).op, ∫⁻ x in D, ‖c * f u (a • x)‖ₑ ∂ν :=
      (Subgroup.equivOp Γ).tsum_eq _
    _ = _ := ((sNormOneFundamentalDomain K S ν).lintegral_eq_tsum''
      (fun x : N => ‖c * f u x‖ₑ)).symm

theorem sourceSLocalProbeOrbit_lintegral_enorm_le (c : ℂ) (u : SWholeUnits K S) :
    (∫⁻ q, ‖c * P u q‖ₑ ∂μ) ≤ sourceSLocalProbeAbsoluteMass K hζ S v c u := by
  have hm : Measurable (fun q : Q => ‖c * P u q‖ₑ) :=
    ((sourceSLocalProbeOrbit_measurable K hζ S v u).const_mul c).enorm
  have hq : Measurable (sNormOneSixthQuotientMap K S) := measurable_quotient_mk''
  change (∫⁻ q, ‖c * P u q‖ₑ ∂((ν).restrict D).map (sNormOneSixthQuotientMap K S)) ≤ _
  rw [lintegral_map hm hq]
  calc
    _ ≤ ∫⁻ x in D, ∑' a : Γ, ‖c * g u a x‖ₑ ∂ν := by
      apply lintegral_mono
      intro x
      change ‖c * P u (sNormOneSixthQuotientMap K S x)‖ₑ ≤ ∑' a : Γ, ‖c * g u a x‖ₑ
      rw [sourceSLocalProbeOrbit_mk, ← tsum_mul_left]
      exact enorm_tsum_le_tsum_enorm
    _ = _ := sourceSLocalProbeOrbit_absoluteMass K hζ S v c u

variable {ι : Type*}

def sourceSLocalProbeOrbitSeries (c : ι → ℂ) (u : ι → SWholeUnits K S) (q : Q) : ℂ :=
  ∑' i, c i * P (u i) q

theorem sourceSLocalProbeOrbitSeries_mk_of_summable
    (c : ι → ℂ) (u : ι → SWholeUnits K S) (x : N)
    (hs : Summable (fun a : ι × Γ => ‖c a.1 * g (u a.1) a.2 x‖)) :
    sourceSLocalProbeOrbitSeries K hζ S v c u (sNormOneSixthQuotientMap K S x) =
      ∑' a : ι × Γ, c a.1 * g (u a.1) a.2 x := by
  unfold sourceSLocalProbeOrbitSeries
  rw [hs.of_norm.tsum_prod]
  apply tsum_congr
  intro i
  rw [sourceSLocalProbeOrbit_mk]
  change c i * (∑' a : Γ, g (u i) a x) = ∑' a : Γ, c i * g (u i) a x
  rw [tsum_mul_left]

variable [Countable ι]

/-- This positive identity precedes all use of rearrangement of complex terms. -/
theorem sourceSLocalProbeOrbitSeries_tonelli (c : ι → ℂ) (u : ι → SWholeUnits K S) :
    (∫⁻ x in D, ∑' a : ι × Γ, ‖c a.1 * g (u a.1) a.2 x‖ₑ ∂ν) =
      ∑' i, sourceSLocalProbeAbsoluteMass K hζ S v (c i) (u i) := by
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  have hm (i : ι) (a : Γ) : Measurable (fun x : N => ‖c i * g (u i) a x‖ₑ) :=
    ((sourceSLocalProbeOrbitTranslate_measurable K hζ S v (u i) a).const_mul (c i)).enorm
  calc
    _ = ∫⁻ x in D, ∑' i : ι, ∑' a : Γ, ‖c i * g (u i) a x‖ₑ ∂ν :=
      lintegral_congr fun _ => ENNReal.tsum_prod'
    _ = _ := by
      rw [lintegral_tsum fun i => (Measurable.tsum (hm i)).aemeasurable]
      exact tsum_congr fun i => sourceSLocalProbeOrbit_absoluteMass K hζ S v (c i) (u i)

theorem sourceSLocalProbeOrbitSeries_ae_summable
    (c : ι → ℂ) (u : ι → SWholeUnits K S)
    (hMass : (∑' i, sourceSLocalProbeAbsoluteMass K hζ S v (c i) (u i)) < ⊤) :
    ∀ᵐ x ∂(ν).restrict D, Summable (fun a : ι × Γ => ‖c a.1 * g (u a.1) a.2 x‖) := by
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  have hm (a : ι × Γ) : Measurable (fun x : N => ‖c a.1 * g (u a.1) a.2 x‖ₑ) :=
    ((sourceSLocalProbeOrbitTranslate_measurable K hζ S v (u a.1) a.2).const_mul (c a.1)).enorm
  have hi : (∫⁻ x in D, ∑' a : ι × Γ, ‖c a.1 * g (u a.1) a.2 x‖ₑ ∂ν) ≠ ⊤ :=
    ((sourceSLocalProbeOrbitSeries_tonelli K hζ S v c u).trans_lt hMass).ne
  filter_upwards [ae_lt_top (Measurable.tsum hm) hi] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

/-- The absolutely justified integral of the orbit series on the normalized quotient. -/
theorem sourceSLocalProbeOrbitSeries_unfold
    (c : ι → ℂ) (u : ι → SWholeUnits K S)
    (hMass : (∑' i, sourceSLocalProbeAbsoluteMass K hζ S v (c i) (u i)) < ⊤) :
    Integrable (sourceSLocalProbeOrbitSeries K hζ S v c u) μ ∧
      (∫ q, sourceSLocalProbeOrbitSeries K hζ S v c u q ∂μ) =
        ∑' i, c i * sourceSLocalProbeSheet K hζ S v (sLocalNorm K S (u i)) := by
  let G (i : ι) (q : Q) := c i * P (u i) q
  have hm (i : ι) : Measurable (G i) :=
    (sourceSLocalProbeOrbit_measurable K hζ S v (u i)).const_mul (c i)
  have hi : (∑' i, ∫⁻ q, ‖G i q‖ₑ ∂μ) < ⊤ :=
    (ENNReal.tsum_le_tsum fun i => sourceSLocalProbeOrbit_lintegral_enorm_le K hζ S v (c i) (u i)).trans_lt hMass
  constructor
  · refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
    change (∫⁻ q, ‖∑' i, G i q‖ₑ ∂μ) < ⊤
    apply (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)).trans_lt
    rw [lintegral_tsum fun i => (hm i).enorm.aemeasurable]
    exact hi
  · change (∫ q, ∑' i, G i q ∂μ) = _
    rw [integral_tsum (fun i => (hm i).aestronglyMeasurable) hi.ne]
    apply tsum_congr
    intro i
    dsimp only [G]
    rw [integral_const_mul, (sourceSLocalProbeOrbit_unfold K hζ S v (u i)).2]

end
end ArtinMatthews.SourcePhysical
