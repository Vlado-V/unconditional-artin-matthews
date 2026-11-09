module

public import ArtinMatthews.SourceKPResidualNativeWeak
public import ArtinMatthews.SourceHyperbolicFlatCoordinates
public import ArtinMatthews.SourceHyperbolicNativeCoefficient
public import ArtinMatthews.SourceEuclideanH1Core
public import ArtinMatthews.SourceLpLocalizedField


set_option backward.privateInPublic true
@[expose] public section

/-! Compact native form localization gives the ordinary Cartesian Sobolev gradient. -/

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical ENNReal
noncomputable section

section CartesianLimits

variable (I : Type*) [Fintype I]

local notation "X" => ProductSpace I
local notation "E" => EuclideanSpace ℝ (I × Fin 3)
local notation "ν" => productVolume I
local notation "e" => productFlatEuclideanEquiv I
local notation "B" => EuclideanSpace.basisFun (I × Fin 3) ℝ
local notation "J" => SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
local notation "D" => EuclideanGradient.CM.Construction.sobolevVectorGradient B
local notation "cF" => (2 * Real.pi * Complex.I : ℂ)

private theorem nativeUnweight_core_partial (f : h1Tests I 2)
    {x : X} (hx : x ∈ productUpper I) (ij : I × Fin 3) :
    productNativeUnweight x (h1GradientAt f x) ij = productPartial f.val ij.1 ij.2 x := by
  obtain ⟨i,j⟩ := ij
  rw [productNativeUnweight, productNativeDiagonal_apply, h1GradientAt_apply,
    Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (productUpper_pos hx i).ne'), one_mul]

private theorem nativeWeightedCoreLimits_cartesian
    (S : Set X) (hS : IsCompact S) (hSupper : S ⊆ productUpper I)
    (M₀ : H1Mass I) (G₀ : H1Gradient I) (f : ℕ → h1Tests I 2)
    (hfS : ∀ n, tsupport (f n).val ⊆ S)
    (hm : Tendsto (fun n => h1TestMass (f n)) atTop (𝓝 M₀))
    (hg : Tendsto (fun n => h1TestGradient (f n)) atTop (𝓝 G₀)) :
    ∃ (w m : Lp ℂ 2 (volume : Measure E)) (g : Lp (H1Vector I) 2 (volume : Measure E)),
      J w = m ∧ cF • D w = g ∧
      ∀ᵐ x ∂(volume : Measure X), x ∈ S →
        m (e x) = M₀ x ∧ g (e x) = productNativeUnweight x (G₀ x) := by
  have hSm := hS.isClosed.measurableSet
  obtain ⟨c,hc,hdom⟩ := productVolume_volume_restrict_le_smul hS hSupper
  obtain ⟨C,_,hC⟩ := productNativeUnweight_bounded hS hSupper
  have hmeas : AEStronglyMeasurable (productNativeUnweight (ι := I)) (volume.restrict S) :=
    productNativeUnweight_measurable.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict S), ‖productNativeUnweight (ι := I) x‖ ≤ C := by
    filter_upwards [ae_restrict_mem hSm] with x hx
    exact hC x hx
  let am (x : X) : ℂ →L[ℝ] ℂ := ContinuousLinearMap.id ℝ ℂ
  have ham : AEStronglyMeasurable am (volume.restrict S) := aestronglyMeasurable_const
  have ham' : ∀ᵐ x ∂(volume.restrict S), ‖am x‖ ≤ ‖ContinuousLinearMap.id ℝ ℂ‖ :=
    Eventually.of_forall fun _ => le_rfl
  let Tm := sourceLpLocalizedField hSm hc hdom am ham ham'
  let Tg := sourceLpLocalizedField hSm hc hdom productNativeUnweight hmeas hbound
  let equiv := (e).toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving equiv volume volume := productFlatEuclideanEquiv_measurePreserving I
  have hinv : MeasurePreserving equiv.symm volume volume := hmp.symm
  let Lm := (Lp.compMeasurePreservingₗᵢ ℝ equiv.symm hinv).toContinuousLinearMap.comp Tm
  let Lg := (Lp.compMeasurePreservingₗᵢ ℝ equiv.symm hinv).toContinuousLinearMap.comp Tg
  have hmcoe (f : H1Mass I) : ∀ᵐ z ∂(volume : Measure E),
      Lm f z = S.indicator f ((e).symm z) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (Tm f) hinv,
      hinv.quasiMeasurePreserving.ae (sourceLpLocalizedField_coe hSm hc hdom am ham ham' f)]
      with z hz hq
    change (Lp.compMeasurePreserving equiv.symm hinv (Tm f)) z = _
    rw [hz]
    exact hq
  have hgcoe (f : H1Gradient I) : ∀ᵐ z ∂(volume : Measure E),
      Lg f z = S.indicator (fun x => productNativeUnweight x (f x)) ((e).symm z) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (Tg f) hinv,
      hinv.quasiMeasurePreserving.ae
        (sourceLpLocalizedField_coe hSm hc hdom productNativeUnweight hmeas hbound f)] with z hz hq
    change (Lp.compMeasurePreserving equiv.symm hinv (Tg f)) z = _
    rw [hz]
    exact hq
  let m := Lm (M₀)
  let g := Lg (G₀)
  let fE (n : ℕ) : E → ℂ := (f n).val ∘ (e).symm
  let fm (n : ℕ) := Lm (h1TestMass (f n))
  let fg (n : ℕ) := Lg (h1TestGradient (f n))
  have hfE (n : ℕ) : ContDiff ℝ 1 (fE n) :=
    ((f n).prop.1.of_le (by norm_num)).comp (e).symm.contDiff
  have hfc (n : ℕ) : HasCompactSupport (fE n) :=
    (f n).prop.2.1.comp_homeomorph (e).symm.toHomeomorph
  have hac : (volume : Measure X).restrict S ≪ ν := Measure.absolutelyContinuous_of_le_smul hdom
  have hma (n : ℕ) : (fm n : E → ℂ) =ᵐ[volume] fE n := by
    have htest := (ae_restrict_iff' hSm).mp (hac.ae_eq (h1TestMass_coe (f n)))
    filter_upwards [hmcoe (h1TestMass (f n)), hinv.quasiMeasurePreserving.ae htest] with z hz ht
    change Lm (h1TestMass (f n)) z = (f n).val ((e).symm z)
    rw [hz]
    by_cases hs : (e).symm z ∈ S
    · rw [Set.indicator_of_mem hs]
      exact ht hs
    · rw [Set.indicator_of_notMem hs, image_eq_zero_of_notMem_tsupport (fun h => hs (hfS n h))]
  have hga (n : ℕ) (ij : I × Fin 3) :
      ∀ᵐ z ∂(volume : Measure E), fg n z ij = fderiv ℝ (fE n) z (B ij) := by
    have htest := (ae_restrict_iff' hSm).mp (hac.ae_eq (h1TestGradient_coe (f n)))
    filter_upwards [hgcoe (h1TestGradient (f n)), hinv.quasiMeasurePreserving.ae htest] with z hz ht
    let x := (e).symm z
    have hd := productFlatEuclideanEquiv_partial I (f n).val x
      ((f n).prop.1.differentiable (by norm_num) x) ij.1 ij.2
    change fderiv ℝ (fE n) (e x) (B ij) = productPartial (f n).val ij.1 ij.2 x at hd
    rw [(e).apply_symm_apply z] at hd
    change Lg (h1TestGradient (f n)) z ij = _
    rw [hz, hd]
    by_cases hs : x ∈ S
    · have htx := ht hs
      change h1TestGradient (f n) x = h1GradientAt (f n) x at htx
      rw [Set.indicator_of_mem hs, htx]
      exact nativeUnweight_core_partial I (f n) (hSupper hs) ij
    · rw [Set.indicator_of_notMem hs, productPartial,
        fderiv_of_notMem_tsupport ℝ (fun h => hs (hfS n h))]
      rfl
  have hfm : Tendsto fm atTop (𝓝 m) := (Lm.continuous.tendsto _).comp hm
  have hfg : Tendsto fg atTop (𝓝 g) := (Lg.continuous.tendsto _).comp hg
  obtain ⟨w,hw,hw'⟩ :=
    sourceEuclideanH1_of_compact_core_limits B fE hfE hfc m g fm fg hfm hfg hma hga
  refine ⟨w,m,g,hw,hw',?_⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae (hmcoe (M₀)),
    hmp.quasiMeasurePreserving.ae (hgcoe (G₀))] with x hx hy hs
  change m (e x) = _ ∧ g (e x) = _
  rw [show m (e x) = S.indicator (M₀) ((e).symm (e x)) from hx,
    show g (e x) = S.indicator (fun y => productNativeUnweight y (G₀ y)) ((e).symm (e x)) from hy,
    (e).symm_apply_apply, Set.indicator_of_mem hs, Set.indicator_of_mem hs]
  exact ⟨rfl,rfl⟩

end CartesianLimits

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "I" => InfinitePlace K
local notation "X" => ProductSpace I
local notation "E" => EuclideanSpace ℝ (I × Fin 3)
local notation "ν" => productVolume I
local notation "e" => productFlatEuclideanEquiv I
local notation "B" => EuclideanSpace.basisFun (I × Fin 3) ℝ
local notation "L" => sourceKPCompactH1Localization K hζ b p
local notation "M" => h1EnergyMass I
local notation "G" => h1EnergyGradient I
local notation "J" => SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
local notation "D" => EuclideanGradient.CM.Construction.sobolevVectorGradient B
local notation "cF" => (2 * Real.pi * Complex.I : ℂ)

theorem sourceKPCompactH1Localization_cartesian
    (η : SourceKPFiniteChartTests K hζ b p) (u : SourceKPCompactH1 K hζ) :
    ∃ (w m : Lp ℂ 2 (volume : Measure E)) (g : Lp (H1Vector I) 2 (volume : Measure E)),
      J w = m ∧ cF • D w = g ∧
      ∀ᵐ x ∂(volume : Measure X), x ∈ tsupport η.val.val →
        m (e x) = M (L η u) x ∧
        g (e x) = productNativeUnweight x (G (L η u) x) := by
  obtain ⟨f,hf,hm,hg⟩ := sourceKPCompactH1Localization_core_seq K hζ b p η u
  exact nativeWeightedCoreLimits_cartesian I _ η.val.prop.2.1 η.val.prop.2.2
    (M (L η u)) (G (L η u)) f hf hm hg

end
end ArtinMatthews
