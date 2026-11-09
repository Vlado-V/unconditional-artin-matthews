module

public import ArtinMatthews.SourceKPTranslateCoreGramGradient
public import ArtinMatthews.SourceKPTranslateTraceIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite Gram trace has bounded native energy and the exact
Dirichlet adjoint given by exchanging its two translations. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "C2" => sourceKPCompactC2Core K hζ
local notation "E" => sourceKPCompactCoreEnergy K hζ
local notation "d[" t "]" => (Subgroup.relIndex (J) (D t) : ℝ)
local notation "π[" t ", " ht "]" => sourceKPTranslateAutomorphicCompactMap K hζ T t ht

private theorem coreDirichlet_trace (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f g : C2) :
    sourceKPCompactDirichletCore K hζ f (sourceKPTranslateCoreGram K hζ T t ht u hu g) =
      ∫ x, sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g x ∂μJ := by
  unfold sourceKPCompactDirichletCore
  rw [sourceKPCompactCorePairDensity_gram_right_eq_trace]
  exact sourceKPTranslateCompactTrace_integral K hζ T t ht _
    (sourceKPTranslateCoreGradientPair_continuous K hζ T t ht u hu f g)
    (sourceKPTranslateCoreGradientPair_integrable K hζ T t ht u hu f g)

theorem sourceKPTranslateCoreGram_dirichlet (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f g : C2) :
    sourceKPCompactDirichletCore K hζ f (sourceKPTranslateCoreGram K hζ T t ht u hu g) =
      sourceKPCompactDirichletCore K hζ (sourceKPTranslateCoreGram K hζ T u hu t ht f) g := by
  rw [coreDirichlet_trace K hζ T t ht u hu f g]
  unfold sourceKPCompactDirichletCore
  rw [sourceKPCompactCorePairDensity_gram_left_eq_trace]
  exact (sourceKPTranslateCompactTrace_integral K hζ T u hu _
    (sourceKPTranslateCoreGradientPair_continuous K hζ T t ht u hu f g)
    (sourceKPTranslateCoreGradientPair_integrable K hζ T t ht u hu f g)).symm

theorem sourceKPTranslateCoreGram_energy_bound (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : C2) :
    (∫ y, E (sourceKPTranslateCoreGram K hζ T t ht u hu g) y ∂μY) ≤
      d[t] * d[u] * ∫ y, E g y ∂μY := by
  let f := sourceKPTranslateCoreGram K hζ T t ht u hu g
  let W := sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g
  let S (v : C2) := ∫ y, E v y ∂μY
  have hE : ((S f : ℝ) : ℂ) = ∫ x, W x ∂μJ :=
    (sourceKPCompactDirichletCore_self K hζ f).symm.trans
      (coreDirichlet_trace K hζ T t ht u hu f g)
  have hS : 0 ≤ S f := integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f)
  have hN := norm_integral_le_integral_norm (μ := μJ) W
  rw [← hE, Complex.norm_real, Real.norm_of_nonneg hS] at hN
  letI : (J).IsFiniteRelIndex (D t) := sourceKPFiniteTranslateLevel_finiteRelIndex_conjugate K hζ T t
  have hd : 0 < d[t] := by
    exact_mod_cast Nat.pos_of_ne_zero (Subgroup.relIndex_ne_zero (H := J) (K := D t))
  let r : ℝ := d[t]⁻¹
  have hr : 0 < r := inv_pos.mpr hd
  have hf := sourceKPTranslateCoreEnergy_pullback_integrable K hζ T t ht f
  have hg := sourceKPTranslateCoreEnergy_pullback_integrable K hζ T u hu g
  have hf' : Integrable (fun x : YJ => r * E f (π[t, ht] x)) μJ := hf.const_mul r
  have hg' : Integrable (fun x : YJ => r⁻¹ * E g (π[u, hu] x)) μJ := hg.const_mul r⁻¹
  have hsum : Integrable (fun x : YJ => (r * E f (π[t, ht] x) + r⁻¹ * E g (π[u, hu] x)) / 2) μJ :=
    (hf'.add hg').div_const 2
  have hbound := hN.trans (integral_mono
    (sourceKPTranslateCoreGradientPair_integrable K hζ T t ht u hu f g).norm hsum
    (sourceKPTranslateCoreGradientPair_norm_le K hζ T t ht u hu f g r hr))
  have hIt := sourceKPTranslateCoreEnergy_pullback_integral K hζ T t ht f
  have hIu := sourceKPTranslateCoreEnergy_pullback_integral K hζ T u hu g
  have hIt' : (∫ x : YJ, E f (π[t, ht] x) ∂μJ) = d[t] * S f := hIt
  have hIu' : (∫ x : YJ, E g (π[u, hu] x) ∂μJ) = d[u] * S g := hIu
  have heq :
      (∫ x : YJ, (r * E f (π[t, ht] x) + r⁻¹ * E g (π[u, hu] x)) / 2 ∂μJ) =
        (S f + d[t] * d[u] * S g) / 2 := by
    rw [integral_div, integral_add hf' hg', integral_const_mul, integral_const_mul, hIt', hIu']
    have hr1 : r * d[t] = 1 := inv_mul_cancel₀ hd.ne'
    have hr2 : r⁻¹ = d[t] := inv_inv _
    rw [← mul_assoc r, hr1, one_mul, hr2, mul_assoc (d[t])]
  rw [heq] at hbound
  change S f ≤ d[t] * d[u] * S g
  linarith

end
end ArtinMatthews
