module

public import ArtinMatthews.SourceSLocalAdditiveFourier
public import ArtinMatthews.SourceComplexMellinSchwartz


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Set
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}
local notation "ArchSupport" => tsupport (sourceComplexProductTest (ι := CPlaces))

private theorem sourceSLocalAdditiveProbe_support_subset :
    Function.support (sourceSLocalAdditiveProbe K S) ⊆
      ArchSupport ×ˢ sourceFiniteUnitAnnulus K S := by
  intro x hx
  change sourceComplexProductTest x.1 * sourceFiniteUnitTest K S x.2 ≠ 0 at hx
  refine ⟨subset_tsupport _ (left_ne_zero_of_mul hx), ?_⟩
  by_contra hn
  exact (right_ne_zero_of_mul hx) (sourceFiniteUnitTest_eq_zero_outside K S x.2 hn)

theorem sourceSLocalAdditiveProbe_tsupport_subset :
    tsupport (sourceSLocalAdditiveProbe K S) ⊆
      ArchSupport ×ˢ sourceFiniteUnitAnnulus K S :=
  closure_minimal (sourceSLocalAdditiveProbe_support_subset K S)
    ((sourceComplexProductTest_compact (ι := CPlaces)).prod
      (sourceFiniteUnitAnnulus_isCompact K S)).isClosed

theorem sourceSLocalAdditiveProbe_compactSupport : HasCompactSupport (sourceSLocalAdditiveProbe K S) :=
  HasCompactSupport.of_support_subset_isCompact
    ((sourceComplexProductTest_compact (ι := CPlaces)).prod (sourceFiniteUnitAnnulus_isCompact K S))
    (sourceSLocalAdditiveProbe_support_subset K S)

theorem sourceSLocalAdditiveProbe_support_away_zero {x : SLocalAdditiveSpace K S}
    (hx : x ∈ tsupport (sourceSLocalAdditiveProbe K S)) :
    (∀ w : CPlaces, x.1 w ≠ 0) ∧ (∀ p : S, x.2 p ≠ 0) := by
  have h := sourceSLocalAdditiveProbe_tsupport_subset K S hx
  exact ⟨sourceComplexProductTest_away_coordinate_zero h.1,
    fun p => sourceLocalUnitAnnulus_ne_zero K p.val (h.2 p (mem_univ p))⟩

theorem sourceSLocalAdditiveProbe_arch_smooth (a : SFiniteSpace K S) :
    ContDiff ℝ ∞ (fun x : CPlaces → ℂ => sourceSLocalAdditiveProbe K S (x, a)) := by
  change ContDiff ℝ ∞ (fun x : CPlaces → ℂ =>
    sourceComplexProductTest x * sourceFiniteUnitTest K S a)
  exact (sourceComplexProductTest_smooth (ι := CPlaces)).mul contDiff_const

theorem sourceSLocalAdditiveProbe_finite_locallyConstant (a : CPlaces → ℂ) :
    IsLocallyConstant (fun x : SFiniteSpace K S => sourceSLocalAdditiveProbe K S (a, x)) := by
  change IsLocallyConstant (fun x : SFiniteSpace K S =>
    sourceComplexProductTest a * sourceFiniteUnitTest K S x)
  exact (IsLocallyConstant.const (X := SFiniteSpace K S) (sourceComplexProductTest a)).mul
    (sourceFiniteUnitTest_locallyConstant K S)

theorem sourceSLocalAdditiveProbe_continuous : Continuous (sourceSLocalAdditiveProbe K S) :=
  ((sourceComplexProductTest_smooth (ι := CPlaces)).continuous.comp continuous_fst).mul
    ((sourceFiniteUnitTest_locallyConstant K S).continuous.comp continuous_snd)

theorem sourceSLocalAdditiveProbe_integrable :
    Integrable (sourceSLocalAdditiveProbe K S) (sourceSLocalAdditiveMeasure K S) := by
  let (p : S) : (sourceLocalSelfDual K p.val).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K p.val
  have : SigmaFinite (sourceFiniteSelfDualMeasure K S) := by
    unfold sourceFiniteSelfDualMeasure
    infer_instance
  have hF : Integrable (sourceFiniteUnitTest K S) (sourceFiniteSelfDualMeasure K S) :=
    Integrable.fintype_prod_dep (μ := fun p : S => sourceLocalSelfDual K p.val) fun p =>
      (sourceLocalUnitTest_locallyConstant K p.val).continuous.integrable_of_hasCompactSupport
        (sourceLocalUnitTest_compactSupport K p.val)
  exact sourceComplexProductTest_integrable.mul_prod hF

theorem sourceLocalUnitTestFourier_eq_zero_outside (P : HeightOneSpectrum (𝓞 K))
    (y : P.adicCompletion K)
    (hy : y ∉ sourceLocalBall K P ((sourceDifferentExponent K P : ℤ) + 1)) :
    sourceLocalFourier K P (sourceLocalUnitTest K P) y = 0 := by
  have hD : y ∉ sourceLocalBall K P (sourceDifferentExponent K P : ℤ) := by
    intro h
    apply hy
    exact (show sourceLocalValuation K P y ≤ WithZero.exp (sourceDifferentExponent K P : ℤ) from h).trans
      (WithZero.exp_le_exp.mpr (le_add_of_nonneg_right (by norm_num)))
  rw [sourceLocalUnitTestFourier_raw, sourceLocalBallIndicator, sourceLocalBallIndicator,
    indicator_of_notMem hD, indicator_of_notMem hy, mul_zero, mul_zero, sub_zero]

theorem sourceLocalUnitTestFourier_tsupport_subset (P : HeightOneSpectrum (𝓞 K)) :
    tsupport (sourceLocalFourier K P (sourceLocalUnitTest K P)) ⊆
      sourceLocalBall K P ((sourceDifferentExponent K P : ℤ) + 1) := by
  apply closure_minimal _ (sourceLocalBall_isCompact K P _).isClosed
  intro y hy
  by_contra hn
  exact hy (sourceLocalUnitTestFourier_eq_zero_outside K P y hn)

theorem sourceLocalUnitTestFourier_locallyConstant (P : HeightOneSpectrum (𝓞 K)) :
    IsLocallyConstant (sourceLocalFourier K P (sourceLocalUnitTest K P)) := by
  have he := funext (sourceLocalUnitTestFourier_raw K P)
  rw [he]
  exact ((IsLocallyConstant.const _).mul (sourceLocalBallIndicator_locallyConstant K P _)).sub
    ((IsLocallyConstant.const _).mul (sourceLocalBallIndicator_locallyConstant K P _))

theorem sourceLocalUnitTestFourier_integrable (P : HeightOneSpectrum (𝓞 K)) :
    Integrable (sourceLocalFourier K P (sourceLocalUnitTest K P)) (sourceLocalSelfDual K P) := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  refine (sourceLocalUnitTestFourier_locallyConstant K P).continuous.integrable_of_hasCompactSupport ?_
  exact (sourceLocalBall_isCompact K P _).of_isClosed_subset isClosed_closure
    (sourceLocalUnitTestFourier_tsupport_subset K P)

variable [IsTotallyComplex K]

theorem sourceSLocalAdditiveProbe_fourier_tsupport_finite :
    tsupport (sourceSLocalAdditiveFourier K S (sourceSLocalAdditiveProbe K S)) ⊆
      Prod.snd ⁻¹' Set.univ.pi (fun p : S =>
        sourceLocalBall K p.val ((sourceDifferentExponent K p.val : ℤ) + 1)) := by
  apply closure_minimal _
    (((isCompact_univ_pi (fun p : S => sourceLocalBall_isCompact K p.val
      ((sourceDifferentExponent K p.val : ℤ) + 1))).isClosed).preimage continuous_snd)
  intro y hy p _
  by_contra hn
  have h0 : sourceLocalFourier K p.val (sourceLocalUnitTest K p.val) (y.2 p) = 0 :=
    sourceLocalUnitTestFourier_eq_zero_outside K p.val (y.2 p) hn
  apply hy
  rw [sourceSLocalAdditiveProbe_fourier_tensor,
    Finset.prod_eq_zero (Finset.mem_univ p) h0, mul_zero]

theorem sourceSLocalAdditiveProbe_fourier_integrable :
    Integrable (sourceSLocalAdditiveFourier K S (sourceSLocalAdditiveProbe K S))
      (sourceSLocalAdditiveMeasure K S) := by
  let (p : S) : (sourceLocalSelfDual K p.val).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K p.val
  have : SigmaFinite (sourceFiniteSelfDualMeasure K S) := by
    unfold sourceFiniteSelfDualMeasure
    infer_instance
  have ha : Integrable (sourceComplexTraceFourier sourceAnnularSchwartzTest) sourceComplexTraceMeasure := by
    have h : Integrable (sourceComplexTraceFourierSchwartz sourceAnnularSchwartzTest)
        sourceComplexTraceMeasure :=
      (sourceComplexTraceFourierSchwartz sourceAnnularSchwartzTest).integrable.smul_measure
        (by norm_num : (2 : ENNReal) ≠ ⊤)
    exact h.congr (Filter.Eventually.of_forall (sourceComplexTraceFourierSchwartz_apply _))
  have hA : Integrable (fun a : CPlaces → ℂ =>
      ∏ w : CPlaces, sourceComplexTraceFourier sourceAnnularSchwartzTest (a w))
      (sourceComplexProductMeasure CPlaces) := Integrable.fintype_prod fun _ => ha
  have hF : Integrable (fun a : SFiniteSpace K S =>
      ∏ p : S, sourceLocalFourier K p.val (sourceLocalUnitTest K p.val) (a p))
      (sourceFiniteSelfDualMeasure K S) :=
    Integrable.fintype_prod_dep (μ := fun p : S => sourceLocalSelfDual K p.val)
      (fun p => sourceLocalUnitTestFourier_integrable K p.val)
  exact (hA.mul_prod hF).congr (Filter.Eventually.of_forall fun y =>
    (sourceSLocalAdditiveProbe_fourier_tensor K S y).symm)

end
end ArtinMatthews.SourcePhysical
