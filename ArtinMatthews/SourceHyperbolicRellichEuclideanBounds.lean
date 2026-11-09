module

public import ArtinMatthews.SourceHyperbolicRellichFlatten
public import ArtinMatthews.SourceHyperbolicRellichWeights


set_option backward.privateInPublic true
@[expose] public section

/-! Transfer the native supported tests and bounds to the Euclidean Rellich chart. -/
namespace ArtinMatthews
open MeasureTheory Set Filter SourceHyperbolicGreen
open scoped Topology ContDiff BigOperators ENNReal Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def sourceHyperbolicFlatTest (f : h1Tests ι 2) : HyperbolicFlatSpace ι → ℂ :=
  f.val ∘ (sourceHyperbolicFlatten ι).symm

theorem sourceHyperbolicFlatTest_contDiff (f : h1Tests ι 2) :
    ContDiff ℝ 1 (sourceHyperbolicFlatTest f) :=
  (f.property.1.of_le (by norm_num)).comp (sourceHyperbolicFlatten ι).symm.contDiff

theorem sourceHyperbolicFlatTest_support (f : h1Tests ι 2) {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hsupp : tsupport f.val ⊆ S) :
    tsupport (sourceHyperbolicFlatTest f) ⊆ sourceHyperbolicFlatten ι '' S := by
  let e := sourceHyperbolicFlatten ι
  apply closure_minimal _ (hS.image e.continuous).isClosed
  intro x hx
  exact ⟨e.symm x,hsupp (subset_tsupport _ hx),e.apply_symm_apply x⟩

theorem sourceHyperbolicFlatTest_hasCompactSupport (f : h1Tests ι 2) {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hsupp : tsupport f.val ⊆ S) :
    HasCompactSupport (sourceHyperbolicFlatTest f) :=
  (hS.image (sourceHyperbolicFlatten ι).continuous).of_isClosed_subset
    (isClosed_tsupport _) (sourceHyperbolicFlatTest_support f hS hsupp)

theorem sourceHyperbolicFlatTest_mass_le (f : h1Tests ι 2) {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hsupp : tsupport f.val ⊆ S) {d : ℝ} (hd : 0 < d)
    (hlo : ENNReal.ofReal d • volume.restrict S ≤ (productVolume ι).restrict S) :
    (∫ x, ‖sourceHyperbolicFlatTest f x‖^2) ≤ ‖h1TestMass f‖^2/d := by
  let e := sourceHyperbolicFlatten ι
  let F := sourceHyperbolicFlatTest f
  have hset : (∫ x in e '' S, ‖F x‖^2) = ∫ p in S, ‖f.val p‖^2 := by
    have h := (sourceHyperbolicFlatten_measurePreserving (ι := ι)).setIntegral_image_emb
      e.toHomeomorph.measurableEmbedding (fun x => ‖F x‖^2) S
    simpa only [F,sourceHyperbolicFlatTest,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using h
  calc
    _ = ∫ x in e '' S, ‖F x‖^2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : F x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (sourceHyperbolicFlatTest_support f hS hsupp h))
      simp [hz]
    _ = ∫ p in S, ‖f.val p‖^2 := hset
    _ ≤ _ := sourceHyperbolicRellich_unweighted_mass_bound f hsupp hd hlo

theorem sourceHyperbolicFlatTest_fderiv_le (f : h1Tests ι 2) {S : Set (ProductSpace ι)}
    (hS : IsCompact S) (hsupp : tsupport f.val ⊆ S)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (hheight : ∀ p ∈ S, ∀ i, a ≤ p i 2)
    (hlo : ENNReal.ofReal d • volume.restrict S ≤ (productVolume ι).restrict S) :
    (∫ x, ‖fderiv ℝ (sourceHyperbolicFlatTest f) x‖^2) ≤
      (Fintype.card (ι × Fin 3) : ℝ) * (‖h1TestGradient f‖^2/(a^2*d)) := by
  let e := sourceHyperbolicFlatten ι
  let F := sourceHyperbolicFlatTest f
  let n : ℝ := Fintype.card (ι × Fin 3)
  let Q : ProductSpace ι → ℝ := fun p => ∑ i, ∑ j : Fin 3, ‖productPartial f.val i j p‖^2
  have hQ : Continuous Q := by
    have hFD : Continuous (fderiv ℝ f.val) := f.property.1.continuous_fderiv (by norm_num)
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    change Continuous (fun p : ProductSpace ι => ‖fderiv ℝ f.val p (productDirection i j)‖^2)
    exact (hFD.clm_apply continuous_const).norm.pow 2
  have hQI : Integrable Q (volume.restrict S) := hQ.continuousOn.integrableOn_compact hS
  have hf : ContDiff ℝ 1 f.val := f.property.1.of_le (by norm_num)
  calc
    _ = ∫ x in e '' S, ‖fderiv ℝ F x‖^2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : fderiv ℝ F x = 0 := fderiv_of_notMem_tsupport ℝ
        (fun h => hx (sourceHyperbolicFlatTest_support f hS hsupp h))
      simp [hz]
    _ = ∫ p in S, ‖fderiv ℝ F (e p)‖^2 :=
      (sourceHyperbolicFlatten_measurePreserving (ι := ι)).setIntegral_image_emb
        e.toHomeomorph.measurableEmbedding (fun x => ‖fderiv ℝ F x‖^2) S
    _ ≤ ∫ p in S, n * Q p :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (hQI.const_mul n) (Filter.Eventually.of_forall (sourceHyperbolicFlatten_fderiv_norm_sq_le hf))
    _ = n * ∫ p in S, Q p := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sourceHyperbolicRellich_unweighted_gradient_bound f hS hsupp ha hd hheight hlo)
      (Nat.cast_nonneg _)

end
end ArtinMatthews
