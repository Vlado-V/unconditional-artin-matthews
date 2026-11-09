module

public import ArtinMatthews.SourceKPDefectHighMean
public import ArtinMatthews.SourceKPCuspAveragingMeasure
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! The literal adelic trace orbit pushes the section product to the
actual high part of the compact automorphic measure. This gives integrable
trace fibres for arbitrary square-integrable representatives. -/

namespace ArtinMatthews
open NumberField MeasureTheory MeasureTheory.Measure Set Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "π" => sourceKPAutomorphicCompactMk K hζ
local notation "μX" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μD" => Measure.restrict (sourceKPAdelicTraceProduct K) (sourceKPAdelicFundamentalDomain K)
local instance sourceKPCompactHighOrbitAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

include hζ in
/-- The actual restricted trace measure has mass one. -/
theorem sourceKPHighTraceDomain_isProbability : IsProbabilityMeasure μD :=
  ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ⟩

variable (A : ℝ)

local notation "Ω" => SourceKPHighCuspFinite K hζ A
local notation "Fsec" => sourceKPCuspBandHighSection K hζ A
local notation "μS" => Measure.restrict (sourceKPHighRepresentativeHaar K hζ A) Fsec

/-- The same literal orbit map used by the normalized high unipotent mean. -/
def sourceKPCompactHighOrbit (x : Ω) (a : 𝔸[K]) : Y :=
  π (sourceKPHighCuspProjection K hζ A (Multiplicative.ofAdd a • x)).val

local notation "orb" => sourceKPCompactHighOrbit K hζ A

/-- The trace domain times the canonical high section maps to the high
restriction of the original compact automorphic measure. -/
theorem sourceKPCompactHighOrbit_measurePreserving (hA : 1 < A) :
    MeasurePreserving (fun z : 𝔸[K] × Ω => orb z.2 z.1) (Measure.prod μD μS)
      (Measure.restrict μY {y | A < sourceKPAutomorphicCompactOrbitHeight K hζ y}) := by
  let H : Set Y := {y | A < sourceKPAutomorphicCompactOrbitHeight K hζ y}
  have hH : MeasurableSet H := measurableSet_lt measurable_const
    (sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous K hζ).measurable
  have hπ := (sourceKPAutomorphicCompactMk_measurePreserving K hζ
    (sourceKPArchHaar K hζ)).restrict_preimage hH
  have hval : MeasurePreserving (Subtype.val : SourceKPHighCuspAutomorphic K hζ A → X)
      (sourceKPHighCuspMeasure K hζ A) (Measure.restrict μX (π ⁻¹' H)) :=
    ⟨measurable_subtype_coe, sourceKPHighCuspMeasure_map_val K hζ A⟩
  obtain ⟨hsec, hinj, hcover⟩ := sourceKPCuspBandHighSection_spec K hζ A
  have horbit := sourceKPCuspHighSection_averaging_measurePreserving K hζ A hA
    Fsec hsec hinj hcover
  exact hπ.comp (hval.comp horbit)

/-- Native `L²` implies actual `L¹` on the trace orbit for almost every
point of the full high representative section. -/
theorem sourceKPCompactHighOrbit_integrable_ae (hA : 1 < A) (F : Y → ℂ)
    (hF : MemLp F 2 μY) :
    ∀ᵐ x ∂μS, IntegrableOn (fun a => F (orb x a)) (sourceKPAdelicFundamentalDomain K)
      (sourceKPAdelicTraceProduct K) := by
  have : IsProbabilityMeasure μD := sourceKPHighTraceDomain_isProbability K hζ
  have hprod : MemLp (fun z : 𝔸[K] × Ω => F (orb z.2 z.1)) 2 (Measure.prod μD μS) :=
    (hF.restrict _).comp_measurePreserving (sourceKPCompactHighOrbit_measurePreserving K hζ A hA)
  have hsq := (memLp_two_iff_integrable_sq_norm hprod.aestronglyMeasurable).1 hprod
  filter_upwards [hprod.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with x hxm hxi
  exact ((memLp_two_iff_integrable_sq_norm hxm).2 hxi).integrable (by norm_num)

/-- Almost-everywhere equality of native representatives descends to the
actual trace fibres on the high section. -/
theorem sourceKPCompactHighOrbit_congr_ae (hA : 1 < A) {F G : Y → ℂ}
    (hFG : F =ᵐ[μY] G) :
    ∀ᵐ x ∂μS, (fun a => F (orb x a)) =ᵐ[μD] (fun a => G (orb x a)) := by
  have : IsProbabilityMeasure μD := sourceKPHighTraceDomain_isProbability K hζ
  have hp := (sourceKPCompactHighOrbit_measurePreserving K hζ A hA).quasiMeasurePreserving
  have hprod := hp.ae_eq_comp (hFG.filter_mono ae_restrict_le)
  have hswap := (measurePreserving_swap (μ := μS) (ν := μD)).quasiMeasurePreserving.ae hprod
  exact ae_ae_of_ae_prod hswap

end
end ArtinMatthews
