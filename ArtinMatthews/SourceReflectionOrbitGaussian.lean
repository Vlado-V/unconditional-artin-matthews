module

public import ArtinMatthews.SourceReflectionRotatedMass
public import ArtinMatthews.SourceThetaWeightedSheet
public import ArtinMatthews.SourceReflectionGaussianSeries
public import ArtinMatthews.SourceSLocalQuotientSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The actual reflected orbit sum unfolds on the quotient and its
Gaussian smoothing can then be taken term by term. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain MeasureTheory SourceReflection SourcePhysical
open scoped NumberField BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (v : InfinitePlace F) {δ : ℝ}
variable {V : Type*} [Fintype V]
variable (D : V → SourceThetaRotatedTensor F (sourceHilbertSet F S₀) hζ v δ)
variable (f : Finset (SourceExteriorPrime F S₀))
local notation "S" => sourceHilbertSet F S₀
local notation "U" => SWholeUnits F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sNormOneQuotientMeasure F S ν
local notation "Idx" => SourceReflectionTermIndex F S₀ f
private def termLength (i : Idx) : ℝ :=
  sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val

local notation "L" => termLength F S₀ f

theorem sourceReflectionRotatedOrbit_integral
    (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (j : Idx → V) (a : Idx → ℂ) (ha : ∀ i, ‖a i‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i)
    (w : Idx → U → ℂ) (hwm : ∀ i, Measurable (w i)) (hw : ∀ i x, ‖w i x‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) (u : Idx → U) (hu : ∀ i, sLocalNorm F S (u i) = L i * T) :
    Integrable (fun q => ∑' i : Idx, sourceSLocalTensorOrbit S
      (sourceReflectionRotatedTerm F S₀ hζ v D f j a w i) (u i) q) μ ∧
    (∫ q, ∑' i : Idx, sourceSLocalTensorOrbit S
      (sourceReflectionRotatedTerm F S₀ hζ v D f j a w i) (u i) q ∂μ) =
      ∑' i : Idx, a i * (D (j i)).weightedSheet 0 (w i) (L i * T) := by
  let _ : Countable Idx := sourceReflectionTermIndex_countable F S₀ f
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar F hζ S v
  let F₀ := sourceReflectionRotatedTerm F S₀ hζ v D f j a w
  obtain ⟨hI,he⟩ := sourceSLocalTensorOrbitSeries_unfold S ν hζ F₀ u
    (fun i => sourceReflectionRotatedTerm_scaled_measurable F S₀ hζ v D f j a w hwm i (u i))
    (sourceReflectionRotatedTerm_totalMass_lt_top F S₀ hζ v D f hδ hσ j a ha w hw T hT u hu)
  refine ⟨hI,he.trans ?_⟩
  apply tsum_congr
  intro i
  rw [hu i]
  unfold SourceThetaRotatedTensor.weightedSheet sourceSLocalSheetProfile F₀ sourceReflectionRotatedTerm
  rw [integral_const_mul]

theorem sourceReflectionRotatedOrbit_gaussian
    (C₀ A₀ : ℝ) (r : ℕ) (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (j : Idx → V) (a : Idx → ℂ) (ha : ∀ i, ‖a i‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i)
    (w : Idx → U → ℂ) (hwm : ∀ i, Measurable (w i)) (hw : ∀ i x, ‖w i x‖ ≤ 1)
    (u : ℝ → Idx → U) (hu : ∀ T, 0 < T → ∀ i, sLocalNorm F S (u T i) = L i * T)
    {R : ℝ} (hR : 0 < R) :
    sourceThetaGaussianProfile C₀ A₀ r (-1)
      (fun T => ∫ q, ∑' i : Idx, sourceSLocalTensorOrbit S
        (sourceReflectionRotatedTerm F S₀ hζ v D f j a w i) (u T i) q ∂μ) R =
      ∑' i : Idx, a i * sourceThetaGaussianProfile C₀ A₀ r (-1)
        ((D (j i)).weightedSheet 0 (w i)) (L i * R) := by
  classical
  let H (i : Idx) := (D (j i)).weightedSheet 0 (w i)
  have hσδ : -δ < σ := by linarith
  choose M hM hb using fun k => (D k).weightedSheet_norm_bound 0 σ hσδ
  let C := ∑ k, M k
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => hM k)
  have hm (i : Idx) : Measurable (fun t : ℝ => H i (Real.exp t)) :=
    (D (j i)).weightedSheet_log_measurable 0 (w i) (hwm i)
  have hB (i : Idx) (T : ℝ) (hT : 0 < T) : ‖H i T‖ ≤ C * T^(-σ) :=
    (hb (j i) (w i) (hw i) T hT).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hM k) (Finset.mem_univ _)) (Real.rpow_nonneg hT.le _))
  let P (T : ℝ) := ∫ q, ∑' i : Idx, sourceSLocalTensorOrbit S
    (sourceReflectionRotatedTerm F S₀ hζ v D f j a w i) (u T i) q ∂μ
  let Q (T : ℝ) := ∑' i : Idx, a i * H i (L i * T)
  have hPQ (T : ℝ) (hT : 0 < T) : P T = Q T :=
    (sourceReflectionRotatedOrbit_integral F S₀ hζ v D f hδ hσ j a ha w hwm hw
      T hT (u T) (hu T hT)).2
  change sourceThetaGaussianProfile C₀ A₀ r (-1) P R = _
  calc
    _ = sourceThetaGaussianProfile C₀ A₀ r (-1) Q R := by
      have hp := sourceThetaGaussianProfile_exp C₀ A₀ r (-1) P (Real.log R)
      have hq := sourceThetaGaussianProfile_exp C₀ A₀ r (-1) Q (Real.log R)
      rw [Real.exp_log hR] at hp hq
      rw [hp, hq, show (fun t => P (Real.exp t)) = (fun t => Q (Real.exp t)) from
        funext (fun t => hPQ _ (Real.exp_pos t))]
    _ = _ := sourceReflectionGaussianProfile_tsum F S₀ f C₀ A₀ r hσ hC a ha H hm hB hR

end
end ArtinMatthews.SourceEulerAssembly
