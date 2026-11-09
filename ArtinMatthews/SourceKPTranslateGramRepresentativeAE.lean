module

public import ArtinMatthews.SourceKPTranslateCoreGramMass
public import ArtinMatthews.SourceKPTranslateRepresentativeAE
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite coset formula for the Haar Gram operators on arbitrary L² input. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace BigOperators Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "XJ" => SourceKPTranslateRepresentativeSpace K hζ T
local notation "q" => sourceKPFiniteLevelToCompact K hζ
local notation "ν" => sourceKPFiniteRepresentativeHaar K hζ
local notation "νJ" => sourceKPTranslateRepresentativeHaar K hζ T
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "C2" => sourceKPCompactC2Core K hζ
local notation "m" => sourceKPCompactCoreMass K hζ 2
local notation "LY" => Lp ℂ 2 μY
local notation "φ[" t ", " ht "]" => sourceKPFiniteRightTranslateMap K hζ T t ht
local notation "L[" t ", " ht ", " b "]" => {c : FJ // φ[t, ht] c = b}

private theorem ae_comp_finite_labels (u : Gf) (hu : J ≤ D u) (p : Y → Prop)
    (hp : ∀ᵐ y ∂μY, p y) : ∀ᵐ x ∂ν, ∀ c : FJ, p (q (x.1,φ[u, hu] c)) := by
  let ρ := sourceKPTranslateRepresentativeMap K hζ T u hu
  have hρ : Measure.QuasiMeasurePreserving ρ νJ ν := by
    refine ⟨sourceKPTranslateRepresentativeMap_measurable K hζ T u hu,?_⟩
    intro S hS
    change Measure.map (sourceKPTranslateRepresentativeMap K hζ T u hu) νJ S = 0
    rw [sourceKPTranslateRepresentativeMap_haar,Measure.smul_apply,hS,smul_zero]
  have hqp := (sourceKPFiniteLevelToCompact_full_quasiMeasurePreserving K hζ).ae hp
  exact sourceKPTranslateRepresentative_ae_forall_coset K hζ T
    (fun x : XJ => p (q (ρ x))) (hρ.ae hqp)

private theorem coreGram_ae (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) (f : C2) :
    (fun x : X => sourceKPTranslateScalarGramL2 K hζ T t ht u hu (m f) (q x)) =ᵐ[ν]
      fun x => ∑ c : L[t, ht, x.2], m f (q (x.1,φ[u, hu] c.val)) := by
  let G := sourceKPTranslateCoreGram K hζ T t ht u hu f
  have hcoe : ∀ᵐ y ∂μY, sourceKPTranslateScalarGramL2 K hζ T t ht u hu (m f) y = G.val y := by
    rw [sourceKPTranslateScalarGramL2_coreMass]
    exact sourceKPCompactCoreMass_coe K hζ G
  have hG := (sourceKPFiniteLevelToCompact_full_quasiMeasurePreserving K hζ).ae hcoe
  have hf := ae_comp_finite_labels K hζ T u hu (fun y => m f y = f.val y)
    (sourceKPCompactCoreMass_coe K hζ f)
  filter_upwards [hG,hf] with x hGx hfx
  rw [hGx]
  let p := sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk x.1)
  have he (b : SourceKPFiniteLevelFiber K hζ) : q (x.1,b) = sourceKPUpperToCompact K hζ b p :=
    (sourceKPUpperToCompact_mk K hζ b x.1).symm
  rw [show q x = sourceKPUpperToCompact K hζ x.2 p from he x.2]
  rw [sourceKPTranslateCoreGram_upper]
  apply Finset.sum_congr rfl
  intro c _
  rw [hfx c.val, he]

theorem sourceKPTranslateScalarGramL2_representative_ae
    (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) (g : LY) :
    (fun x : X => sourceKPTranslateScalarGramL2 K hζ T t ht u hu g (q x)) =ᵐ[ν]
      fun x => ∑ c : L[t, ht, x.2], g (q (x.1,φ[u, hu] c.val)) := by
  let A := sourceKPTranslateScalarGramL2 K hζ T t ht u hu
  obtain ⟨v,hvr,hv⟩ := mem_closure_iff_seq_limit.mp (sourceKPCompactCoreMass_denseRange K hζ g)
  choose f hf using hvr
  have hmass : Tendsto (fun n => m (f n)) atTop (𝓝 g) := by
    rw [funext hf]
    exact hv
  obtain ⟨a,ha,hca⟩ := (tendstoInMeasure_of_tendsto_Lp hmass).exists_seq_tendsto_ae
  have hA : Tendsto (fun n => A (m (f (a n)))) atTop (𝓝 (A g)) :=
    A.continuous.continuousAt.tendsto.comp (hmass.comp ha.tendsto_atTop)
  obtain ⟨b,hb,hcb⟩ := (tendstoInMeasure_of_tendsto_Lp hA).exists_seq_tendsto_ae
  have hAx := (sourceKPFiniteLevelToCompact_full_quasiMeasurePreserving K hζ).ae hcb
  have hfx := ae_comp_finite_labels K hζ T u hu
    (fun y => Tendsto (fun n => m (f (a n)) y) atTop (𝓝 (g y))) hca
  have hcore := ae_all_iff.mpr (fun n : ℕ => coreGram_ae K hζ T t ht u hu (f (a (b n))))
  filter_upwards [hAx,hfx,hcore] with x hAx hfx hcore
  have hlim : Tendsto (fun n => ∑ c : L[t, ht, x.2], m (f (a (b n))) (q (x.1,φ[u, hu] c.val)))
      atTop (𝓝 (∑ c : L[t, ht, x.2], g (q (x.1,φ[u, hu] c.val)))) :=
    tendsto_finsetSum _ (fun c _ => (hfx c.val).comp hb.tendsto_atTop)
  rw [← funext hcore] at hlim
  exact tendsto_nhds_unique hAx hlim

end
end ArtinMatthews
