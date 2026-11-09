module

public import ArtinMatthews.SourceEisensteinHighOutgoingL2


set_option backward.privateInPublic true
@[expose] public section

/-! Exact dyadic volume transport on the actual automorphic high cusp. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceEisensteinShellVolumeMeasurable : MeasurableSpace X := borel X
local instance sourceEisensteinShellVolumeBorel : BorelSpace X := ⟨rfl⟩
local notation "μ" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ

theorem sourceKPDyadicOpenShell_measurable (T : ℝ) (n : ℕ) :
    MeasurableSet (dyadicL2OpenShell H T n) :=
  (sourceKPHighCuspAutomorphic_isOpen K hζ (T*2^n)).measurableSet.inter
    (sourceKPAutomorphicOrbitHeight_sublevel_closed K hζ (T*2^(n+1))).measurableSet

theorem sourceKPDyadicOpenShell_measure_lt_top (T : ℝ) (n : ℕ) :
    μ (dyadicL2OpenShell H T n) < ∞ :=
  lt_of_le_of_lt (measure_mono fun _ hx => hx.2)
    (sourceKPAutomorphicOrbitHeight_sublevel_isCompact K hζ (T*2^(n+1))).measure_lt_top

theorem sourceKPDyadicOpenShell_real_volume (T : ℝ) (hT : 1 < T) (n : ℕ) :
    (2 : ℝ)^n * (μ).real (dyadicL2OpenShell H T n) = (μ).real (dyadicL2OpenShell H T 0) := by
  let t := sourceKPDyadicRadialTime K n
  let c := sourceKPRadialHeightScale K t
  have hc : 0 < c := sourceKPRadialHeightScale_pos K t
  have hcs : c = (2 : ℝ)^n := sourceKPDyadicRadialTime_scale K n
  have hc₁ : 1 ≤ c := by
    rw [hcs]
    exact one_le_pow₀ (by norm_num)
  have hT₀ : 0 < T := zero_lt_one.trans hT
  have hTc : T ≤ c*T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ hT₀.le
  let ν := (sourceKPHighCuspMeasure K hζ T).restrict {x | H x.val ≤ T*2}
  let V := sourceKPHighCuspRadialValue K hζ t T hT
  have hV : Measurable V :=
    ((sourceKPHighCuspRadialValue_continuous K hζ T hT).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hm := sourceKPHighCuspRadialValue_shell_map K hζ t T (T*2) hT (hT.trans_le hTc)
  have hlo : c*T = T*2^n := hcs ▸ mul_comm _ _
  have hhi : c*(T*2) = T*2^(n+1) := by rw [hcs,pow_succ]; ring
  change Measure.map V ν = ENNReal.ofReal c •
    (μ).restrict {x | c*T < H x ∧ H x ≤ c*(T*2)} at hm
  rw [hlo,hhi] at hm
  change Measure.map V ν = ENNReal.ofReal c • (μ).restrict (dyadicL2OpenShell H T n) at hm
  have hb := sourceKPHighCuspMeasure_map_val_restrict K hζ T (T*2)
  have hz : dyadicL2OpenShell H T 0 = {x | T < H x ∧ H x ≤ T*2} := by
    simp only [dyadicL2OpenShell,pow_zero,mul_one,Nat.zero_add,pow_one]
  change Measure.map Subtype.val ν = (μ).restrict {x | T < H x ∧ H x ≤ T*2} at hb
  rw [← hz] at hb
  have hv := congrArg (fun m : Measure X => m.real Set.univ) hm
  have hb' := congrArg (fun m : Measure X => m.real Set.univ) hb
  change (Measure.map V ν).real Set.univ = _ at hv
  change (Measure.map Subtype.val ν).real Set.univ = _ at hb'
  rw [map_measureReal_apply hV MeasurableSet.univ,preimage_univ,
    measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal hc.le] at hv
  rw [map_measureReal_apply measurable_subtype_coe MeasurableSet.univ,preimage_univ] at hb'
  have he : c * (μ).real (dyadicL2OpenShell H T n) = (μ).real (dyadicL2OpenShell H T 0) := by
    simpa only [measureReal_restrict_apply_univ] using hv.symm.trans hb'
  exact hcs ▸ he

theorem sourceKPDyadicOpenShell_real_volume_le (T : ℝ) (hT : 1 < T) (n : ℕ) :
    (μ).real (dyadicL2OpenShell H T n) ≤ (μ).real (dyadicL2OpenShell H T 0) := by
  rw [← sourceKPDyadicOpenShell_real_volume K hζ T hT n]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n))
    (measureReal_nonneg : 0 ≤ (μ).real (dyadicL2OpenShell H T n))

end
end ArtinMatthews
