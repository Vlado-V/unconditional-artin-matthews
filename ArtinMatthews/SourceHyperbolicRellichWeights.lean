module

public import ArtinMatthews.SourceHyperbolicH1CoreEnergy
public import ArtinMatthews.SourceHyperbolicH1LocalMassNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Native height, density, mass and energy comparisons on a compact upper chart. -/
namespace ArtinMatthews
open MeasureTheory Set Filter OAI.CubicEisenstein SourceHyperbolicGreen
open scoped Topology ContDiff BigOperators ENNReal Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem sourceHyperbolicRellich_height_lower [Nonempty ι] {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hSu : S ⊆ productUpper ι) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ S, ∀ i, a ≤ p i 2 := by
  choose a ha hlow using fun i : ι => hS.exists_forall_le'
    (show ContinuousOn (fun p : ProductSpace ι => p i 2) S by fun_prop)
    (fun p hp => productUpper_pos (hSu hp) i)
  refine ⟨Finset.univ.inf' Finset.univ_nonempty a,
    (Finset.lt_inf'_iff _).2 (fun i _ => ha i),?_⟩
  intro p hp i
  exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (hlow i p hp)

theorem sourceHyperbolicRellich_density_pos {p : ProductSpace ι} (hp : p ∈ productUpper ι) :
    0 < h1RealDensity p := by
  unfold h1RealDensity
  exact Finset.prod_pos (fun i _ => inv_pos.mpr (pow_pos (productUpper_pos hp i) 3))

theorem sourceHyperbolicRellich_density_bounds {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hSu : S ⊆ productUpper ι) :
    ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧
      ENNReal.ofReal d • volume.restrict S ≤ (productVolume ι).restrict S ∧
      (productVolume ι).restrict S ≤ ENNReal.ofReal C • volume.restrict S := by
  have hcont := h1RealDensity_continuousOn.mono hSu
  obtain ⟨d,hd,hlow⟩ := hS.exists_forall_le' hcont
    (fun p hp => sourceHyperbolicRellich_density_pos (hSu hp))
  obtain ⟨C,hC⟩ := hS.bddAbove_image hcont
  have he : (productVolume ι).restrict S = (volume.restrict S).withDensity (productDensity (ι := ι)) := by
    rw [productVolume_eq_density, restrict_withDensity hS.measurableSet,
      Measure.restrict_restrict hS.measurableSet, Set.inter_eq_left.mpr hSu]
  refine ⟨d,max C 0,hd,le_max_right _ _,?_⟩
  constructor
  · rw [he, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS.measurableSet] with p hp
    rw [productDensity_eq_ofReal (hSu hp)]
    exact ENNReal.ofReal_le_ofReal (hlow p hp)
  · rw [he, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS.measurableSet] with p hp
    rw [productDensity_eq_ofReal (hSu hp)]
    exact ENNReal.ofReal_le_ofReal ((hC ⟨p,hp,rfl⟩).trans (le_max_left _ _))

theorem sourceHyperbolicRellich_mass_restrict (f : h1Tests ι 2) {S : Set (ProductSpace ι)}
    (hsupp : tsupport f.val ⊆ S) :
    ‖h1TestMass f‖^2 = ∫ p in S, ‖f.val p‖^2 ∂productVolume ι := by
  rw [h1TestMass_norm_sq]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))]
  simp

theorem sourceHyperbolicRellich_energy_restrict (f : h1Tests ι 2) {S : Set (ProductSpace ι)}
    (hsupp : tsupport f.val ⊆ S) :
    ‖h1TestGradient f‖^2 = ∫ p in S, productGradientEnergy f.val p ∂productVolume ι := by
  rw [h1TestGradient_norm_sq]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hz : fderiv ℝ f.val p = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hp (hsupp h))
  simp [productGradientEnergy,productPartial,hz]

theorem sourceHyperbolicRellich_unweighted_mass_bound (f : h1Tests ι 2)
    {S : Set (ProductSpace ι)} (hsupp : tsupport f.val ⊆ S) {d : ℝ} (hd : 0 < d)
    (hlo : ENNReal.ofReal d • volume.restrict S ≤ (productVolume ι).restrict S) :
    (∫ p in S, ‖f.val p‖^2) ≤ ‖h1TestMass f‖^2/d := by
  have hi : Integrable (fun p => ‖f.val p‖^2) (productVolume ι) :=
    (memLp_two_iff_integrable_sq_norm f.property.1.continuous.aestronglyMeasurable).mp
      (h1_compact_memLp f.property.1.continuous f.property.2.1 f.property.2.2 2)
  have h := integral_mono_measure hlo (Filter.Eventually.of_forall (fun p => sq_nonneg ‖f.val p‖)) hi.restrict
  rw [integral_smul_measure,ENNReal.toReal_ofReal hd.le,smul_eq_mul,
    ← sourceHyperbolicRellich_mass_restrict f hsupp] at h
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using h)

theorem sourceHyperbolicRellich_weighted_mass_bound (f : h1Tests ι 2)
    {S : Set (ProductSpace ι)} (hS : IsCompact S) (hsupp : tsupport f.val ⊆ S) {C : ℝ} (hC : 0 ≤ C)
    (hhi : (productVolume ι).restrict S ≤ ENNReal.ofReal C • volume.restrict S) :
    ‖h1TestMass f‖^2 ≤ C * ∫ p in S, ‖f.val p‖^2 := by
  have hi : Integrable (fun p => ‖f.val p‖^2) (volume.restrict S) :=
    (f.property.1.continuous.norm.pow 2).continuousOn.integrableOn_compact hS
  have h := integral_mono_measure hhi (Filter.Eventually.of_forall (fun p => sq_nonneg ‖f.val p‖))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hC,smul_eq_mul,
    ← sourceHyperbolicRellich_mass_restrict f hsupp] at h
  exact h

theorem sourceHyperbolicRellich_unweighted_gradient_bound (f : h1Tests ι 2)
    {S : Set (ProductSpace ι)} (hS : IsCompact S) (hsupp : tsupport f.val ⊆ S)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (hheight : ∀ p ∈ S, ∀ i, a ≤ p i 2)
    (hlo : ENNReal.ofReal d • volume.restrict S ≤ (productVolume ι).restrict S) :
    (∫ p in S, ∑ i, ∑ j : Fin 3, ‖productPartial f.val i j p‖^2) ≤
      ‖h1TestGradient f‖^2/(a^2*d) := by
  let Q : ProductSpace ι → ℝ := fun p => ∑ i, ∑ j : Fin 3, ‖productPartial f.val i j p‖^2
  let E := productGradientEnergy f.val
  have hQcont : Continuous Q := by
    have hFD : Continuous (fderiv ℝ f.val) := f.property.1.continuous_fderiv (by norm_num)
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact ((hFD.clm_apply (continuous_const : Continuous (fun _ : ProductSpace ι => productDirection i j))).norm.pow 2)
  have hQ : Integrable Q (volume.restrict S) := hQcont.continuousOn.integrableOn_compact hS
  have hEμ : Integrable E ((productVolume ι).restrict S) :=
    (productGradientEnergy_integrable f.property.1 f.property.2.1 f.property.2.2).restrict
  have hEvol : Integrable E (volume.restrict S) :=
    (integrable_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hd)) ENNReal.ofReal_ne_top).mp
      (hEμ.mono_measure hlo)
  have hp (p : ProductSpace ι) (hp : p ∈ S) : a^2 * Q p ≤ E p := by
    unfold Q E productGradientEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le (hheight p hp i) 2)
      (Finset.sum_nonneg (fun j _ => sq_nonneg ‖productPartial f.val i j p‖))
  have hQE : a^2 * (∫ p in S, Q p) ≤ ∫ p in S, E p := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hQ.const_mul _) hEvol
    filter_upwards [ae_restrict_mem hS.measurableSet] with p hpS
    exact hp p hpS
  have hE := integral_mono_measure hlo
    (Filter.Eventually.of_forall (productGradientEnergy_nonneg f.val)) hEμ
  rw [integral_smul_measure,ENNReal.toReal_ofReal hd.le,smul_eq_mul,
    ← sourceHyperbolicRellich_energy_restrict f hsupp] at hE
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos ha) hd)).mpr
  calc
    _ = d * (a^2 * ∫ p in S, Q p) := by ring
    _ ≤ d * ∫ p in S, E p := mul_le_mul_of_nonneg_left hQE hd.le
    _ ≤ _ := hE

end
end ArtinMatthews
