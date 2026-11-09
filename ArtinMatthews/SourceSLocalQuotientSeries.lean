module

public import ArtinMatthews.SourceSLocalTensorOrbitReflection


set_option backward.privateInPublic true
@[expose] public section

/-! Tonelli and Bochner unfolding on the actual quotient for a
countable family of tensors with finite total absolute sheet mass. -/
namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical ENNReal
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]
local notation "N" => SNormOne K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "U" => SWholeUnits K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "D" => sNormOneFundamentalSet K S
local notation "μ" => sNormOneQuotientMeasure K S ν
local notation "P" => sNormOnePeriodize K S
local notation "qmk" => sNormOneSixthQuotientMap K S

theorem sNormOnePeriodize_measurable (f : N → ℂ) (hf : Measurable f) : Measurable (P f) := by
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  exact quotientPeriodize_measurable Γ f hf

theorem sNormOnePeriodize_absoluteMass (f : N → ℂ) (hf : Measurable f) :
    (∫⁻ x in D, ∑' γ : (Γ).op, ‖f (γ • x)‖ₑ ∂ν) = ∫⁻ x, ‖f x‖ₑ ∂ν := by
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  have hm (γ : (Γ).op) : Measurable (fun x : N => ‖f (γ • x)‖ₑ) :=
    (hf.comp (measurable_const_smul γ)).enorm
  rw [lintegral_tsum fun γ => (hm γ).aemeasurable]
  exact ((sNormOneFundamentalDomain K S ν).lintegral_eq_tsum'' (fun x : N => ‖f x‖ₑ)).symm

theorem sNormOnePeriodize_lintegral_enorm_le (f : N → ℂ) (hf : Measurable f) :
    (∫⁻ q, ‖P f q‖ₑ ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := by
  have hm := (sNormOnePeriodize_measurable S f hf).enorm
  have hq : Measurable (sNormOneSixthQuotientMap K S) := measurable_quotient_mk''
  change (∫⁻ q, ‖P f q‖ₑ ∂(ν.restrict D).map qmk) ≤ _
  rw [lintegral_map hm hq]
  calc
    _ ≤ ∫⁻ x in D, ∑' γ : (Γ).op, ‖f (γ • x)‖ₑ ∂ν := by
      apply lintegral_mono
      intro x
      change ‖P f (qmk x)‖ₑ ≤ ∑' γ : (Γ).op, ‖f (γ • x)‖ₑ
      rw [sNormOnePeriodize_mk]
      exact enorm_tsum_le_tsum_enorm
    _ = _ := sNormOnePeriodize_absoluteMass S ν f hf

variable {ι : Type*}

def sNormOnePeriodizeSeries (f : ι → N → ℂ) (q : Q) : ℂ :=
  ∑' i, P (f i) q

theorem sNormOnePeriodizeSeries_mk_of_summable (f : ι → N → ℂ) (x : N)
    (hs : Summable (fun a : ι × Γ => ‖f a.1 (x * a.2.val)‖)) :
    sNormOnePeriodizeSeries S f (qmk x) = ∑' a : ι × Γ, f a.1 (x * a.2.val) := by
  rw [sNormOnePeriodizeSeries, hs.of_norm.tsum_prod]
  exact tsum_congr fun i => sNormOnePeriodize_mk_group S (f i) x

variable [Countable ι]

theorem sNormOnePeriodizeSeries_tonelli (f : ι → N → ℂ) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x in D, ∑' a : ι × (Γ).op, ‖f a.1 (a.2 • x)‖ₑ ∂ν) =
      ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂ν := by
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  have hm (i : ι) (γ : (Γ).op) : Measurable (fun x : N => ‖f i (γ • x)‖ₑ) :=
    ((hf i).comp (measurable_const_smul γ)).enorm
  calc
    _ = ∫⁻ x in D, ∑' i : ι, ∑' γ : (Γ).op, ‖f i (γ • x)‖ₑ ∂ν :=
      lintegral_congr fun _ => ENNReal.tsum_prod'
    _ = _ := by
      rw [lintegral_tsum fun i => (Measurable.tsum (hm i)).aemeasurable]
      exact tsum_congr fun i => sNormOnePeriodize_absoluteMass S ν (f i) (hf i)

theorem sNormOnePeriodizeSeries_ae_summable (f : ι → N → ℂ) (hf : ∀ i, Measurable (f i))
    (hMass : (∑' i, ∫⁻ x, ‖f i x‖ₑ ∂ν) < ⊤) :
    ∀ᵐ x ∂ν.restrict D, Summable (fun a : ι × Γ => ‖f a.1 (x * a.2.val)‖) := by
  let : Countable Γ := sNormOneSixthSubgroup_countable K S
  have hm (a : ι × (Γ).op) : Measurable (fun x : N => ‖f a.1 (a.2 • x)‖ₑ) :=
    ((hf a.1).comp (measurable_const_smul a.2)).enorm
  have hfin : (∫⁻ x in D, ∑' a : ι × (Γ).op, ‖f a.1 (a.2 • x)‖ₑ ∂ν) ≠ ⊤ :=
    ((sNormOnePeriodizeSeries_tonelli S ν f hf).trans_lt hMass).ne
  filter_upwards [ae_lt_top (Measurable.tsum hm) hfin] with x hx
  have h := tsum_enorm_ne_top_iff_summable_norm.mp hx.ne
  exact ((Equiv.refl ι).prodCongr (Subgroup.equivOp Γ)).summable_iff.mpr h

theorem sNormOnePeriodizeSeries_unfold (f : ι → N → ℂ) (hf : ∀ i, Measurable (f i))
    (hMass : (∑' i, ∫⁻ x, ‖f i x‖ₑ ∂ν) < ⊤) :
    Integrable (sNormOnePeriodizeSeries S f) μ ∧
      (∫ q, sNormOnePeriodizeSeries S f q ∂μ) = ∑' i, ∫ x, f i x ∂ν := by
  have hm (i : ι) : Measurable (P (f i)) := sNormOnePeriodize_measurable S (f i) (hf i)
  have hfi (i : ι) : Integrable (f i) ν :=
    ⟨(hf i).aestronglyMeasurable,
      (ENNReal.le_tsum (f := fun j => ∫⁻ x, ‖f j x‖ₑ ∂ν) i).trans_lt hMass⟩
  have hQ : (∑' i, ∫⁻ q, ‖P (f i) q‖ₑ ∂μ) < ⊤ :=
    (ENNReal.tsum_le_tsum fun i => sNormOnePeriodize_lintegral_enorm_le S ν (f i) (hf i)).trans_lt hMass
  constructor
  · refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
    change (∫⁻ q, ‖∑' i, P (f i) q‖ₑ ∂μ) < ⊤
    apply (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)).trans_lt
    rw [lintegral_tsum fun i => (hm i).enorm.aemeasurable]
    exact hQ
  · unfold sNormOnePeriodizeSeries
    rw [integral_tsum (fun i => (hm i).aestronglyMeasurable) hQ.ne]
    exact tsum_congr fun i => (sNormOnePeriodize_unfold K S ν (f i) (hf i) (hfi i)).2

theorem sourceSLocalTensorOrbitSeries_unfold {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (F : ι → U → ℂ) (u : ι → U) (hf : ∀ i, Measurable (fun x : N => F i ((x : U) * u i)))
    (hMass : (∑' i, ∫⁻ x : N, ‖F i ((x : U) * u i)‖ₑ ∂ν) < ⊤) :
    Integrable (fun q => ∑' i, sourceSLocalTensorOrbit S (F i) (u i) q) μ ∧
      (∫ q, ∑' i, sourceSLocalTensorOrbit S (F i) (u i) q ∂μ) =
        ∑' i, sourceSLocalSheetProfile S ν hζ (F i) (sLocalNorm K S (u i)) := by
  obtain ⟨hi, heq⟩ := sNormOnePeriodizeSeries_unfold S ν
    (fun i x => F i ((x : U) * u i)) hf hMass
  refine ⟨hi, heq.trans ?_⟩
  apply tsum_congr
  intro i
  apply sourceSLocal_sameNorm_integral S ν (F i)
  exact (sLocalPositiveScaling_norm K hζ S (sLocalNorm_pos K S (u i))).symm

end
end ArtinMatthews.SourcePhysical
