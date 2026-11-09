module

public import ArtinMatthews.SourceReflectionOrbitGaussian
public import ArtinMatthews.SourceReflectionNumeratorSeries
public import Mathlib.Data.Fintype.BigOperators


set_option backward.privateInPublic true
@[expose] public section

/-! The finite retained labels can be carried inside the absolutely
convergent reflected orbit, on the exact supported numerator carrier. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain MeasureTheory SourceReflection SourcePhysical
open scoped NumberField Classical BigOperators ENNReal
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (v : InfinitePlace F) {δ : ℝ}
variable {V X : Type*} [Fintype V] [Fintype X]
variable (D : V → SourceThetaRotatedTensor F (sourceHilbertSet F S₀) hζ v δ)
variable (f : Finset (SourceExteriorPrime F S₀))
variable (d : SourcePrimeExponents F S₀)

local notation "S" => sourceHilbertSet F S₀
local notation "U" => SWholeUnits F S
local notation "Y" => SNormOne F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sNormOneQuotientMeasure F S ν
local notation "Idx" => SourceReflectionTermIndex F S₀ f
local notation "I" => SourceReflectionSupportedTermIndex F S₀ f d × X
private def supportedTermLength (i : Idx) : ℝ :=
  sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val

local notation "L" => supportedTermLength F S₀ f

theorem sourceReflectionRotatedOrbit_supportedFiniteMass
    (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (j : X → Idx → V) (a : X → Idx → ℂ)
    (ha : ∀ x i, ‖a x i‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i)
    (w : X → Idx → U → ℂ) (hw : ∀ x i z, ‖w x i z‖ ≤ 1)
    (u : X → ℝ → Idx → U)
    (hu : ∀ x T, 0 < T → ∀ i, sLocalNorm F S (u x T i) = L i * T)
    (T : ℝ) (hT : 0 < T) :
    (∑' i : I, ∫⁻ y : Y, ‖sourceReflectionRotatedTerm F S₀ hζ v D f
      (j i.2) (a i.2) (w i.2) i.1.val ((y : U) * u i.2 T i.1.val)‖ₑ ∂ν) < ⊤ := by
  let m (x : X) (i : Idx) :=
    ∫⁻ y : Y, ‖sourceReflectionRotatedTerm F S₀ hζ v D f (j x) (a x) (w x) i
      ((y : U) * u x T i)‖ₑ ∂ν
  have hm (x : X) : (∑' i : Idx, m x i) < ⊤ :=
    sourceReflectionRotatedTerm_totalMass_lt_top F S₀ hζ v D f hδ hσ
      (j x) (a x) (ha x) (w x) (hw x) T hT (u x T) (hu x T hT)
  change (∑' i : I, m i.2 i.1.val) < ⊤
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm, tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro x _
  exact (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (m x)).trans_lt (hm x)

set_option maxHeartbeats 500000 in
theorem sourceReflectionRotatedOrbit_supportedFiniteGaussian
    (C₀ A₀ : ℝ) (r : ℕ) (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (j : X → Idx → V) (a : X → Idx → ℂ)
    (ha : ∀ x i, ‖a x i‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i)
    (w : X → Idx → U → ℂ) (hwm : ∀ x i, Measurable (w x i))
    (hw : ∀ x i z, ‖w x i z‖ ≤ 1)
    (u : X → ℝ → Idx → U) (hu : ∀ x T, 0 < T → ∀ i, sLocalNorm F S (u x T i) = L i * T)
    {R : ℝ} (hR : 0 < R) :
    sourceThetaGaussianProfile C₀ A₀ r (-1)
      (fun T => ∫ q, ∑' i : I, sourceSLocalTensorOrbit S
        (sourceReflectionRotatedTerm F S₀ hζ v D f (j i.2) (a i.2) (w i.2) i.1.val)
        (u i.2 T i.1.val) q ∂μ) R =
      ∑' i : I, a i.2 i.1.val * sourceThetaGaussianProfile C₀ A₀ r (-1)
        ((D (j i.2 i.1.val)).weightedSheet 0 (w i.2 i.1.val)) (L i.1.val * R) := by
  let _ : Countable Idx := sourceReflectionTermIndex_countable F S₀ f
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar F hζ S v
  let A (i : I) := a i.2 i.1.val
  let H (i : I) := (D (j i.2 i.1.val)).weightedSheet 0 (w i.2 i.1.val)
  let term (i : I) := sourceReflectionRotatedTerm F S₀ hζ v D f (j i.2) (a i.2) (w i.2) i.1.val
  have hmass (T : ℝ) (hT : 0 < T) :=
    sourceReflectionRotatedOrbit_supportedFiniteMass F S₀ hζ v D f d
      hδ hσ j a ha w hw u hu T hT
  have hI (T : ℝ) (hT : 0 < T) :
      (∫ q, ∑' i : I, sourceSLocalTensorOrbit S (term i) (u i.2 T i.1.val) q ∂μ) =
        ∑' i : I, A i * H i (L i.1.val * T) := by
    obtain ⟨_, he⟩ := sourceSLocalTensorOrbitSeries_unfold S ν hζ term (fun i => u i.2 T i.1.val)
      (fun i => sourceReflectionRotatedTerm_scaled_measurable F S₀ hζ v D f
        (j i.2) (a i.2) (w i.2) (hwm i.2) i.1.val (u i.2 T i.1.val))
      (hmass T hT)
    refine he.trans (tsum_congr ?_)
    intro i
    rw [hu i.2 T hT]
    unfold H SourceThetaRotatedTensor.weightedSheet sourceSLocalSheetProfile term sourceReflectionRotatedTerm
    rw [integral_const_mul]
  have hσδ : -δ < σ := by linarith
  choose M hM hb using fun k => (D k).weightedSheet_norm_bound 0 σ hσδ
  let C := ∑ k, M k
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => hM k)
  have hH (i : I) : Measurable (fun t : ℝ => H i (Real.exp t)) :=
    (D (j i.2 i.1.val)).weightedSheet_log_measurable 0 (w i.2 i.1.val) (hwm _ _)
  have hB (i : I) (t : ℝ) (ht : 0 < t) : ‖H i t‖ ≤ C * t^(-σ) :=
    (hb (j i.2 i.1.val) (w i.2 i.1.val) (hw _ _) t ht).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hM k) (Finset.mem_univ _)) (Real.rpow_nonneg ht.le _))
  let z := Real.log R
  let l (i : I) := Real.log (L i.1.val)
  let E₀ (_ : I) (t : ℝ) := C * Real.exp (-σ*t)
  have hL (i : Idx) : 0 < L i := zero_lt_one.trans_le (sourceReflectionTermLength_one_le F S₀ _ _ _)
  have hl (i : I) : Real.exp (l i) = L i.1.val := Real.exp_log (hL i.1.val)
  have hsum (x : X) : Summable (fun i : Idx => ‖a x i‖ * Real.exp (-σ * Real.log (L i))) := by
    refine (sourceReflectionCoefficient_summable F S₀ f hσ (a x) (ha x)).congr ?_
    intro i
    change ‖a x i‖ * (L i)^(-σ) = _
    rw [Real.rpow_def_of_pos (hL i), mul_comm (Real.log (L i))]
  have hsum' : Summable (fun i : I => ‖A i‖ * Real.exp (-σ * l i)) := by
    have hfull : Summable (fun i : X × Idx => ‖a i.1 i.2‖ * Real.exp (-σ * Real.log (L i.2))) :=
      (summable_prod_of_nonneg (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).2
        ⟨hsum, Summable.of_finite⟩
    let inj (i : I) : X × Idx := (i.2, i.1.val)
    have hInj : Function.Injective inj := by
      intro i i' h
      exact Prod.ext (Subtype.ext (congrArg Prod.snd h)) (congrArg Prod.fst h)
    change Summable ((fun i : X × Idx => ‖a i.1 i.2‖ * Real.exp (-σ * Real.log (L i.2))) ∘ inj)
    exact hfull.comp_injective hInj
  have hsm := sourceThetaGaussianLogSmooth_sum_integral C₀ A₀ r (-1) σ C z A l E₀
    (fun _ => by unfold E₀; fun_prop) (fun _ _ => mul_nonneg hC (Real.exp_pos _).le)
    (fun _ _ => le_rfl) hsum' (fun i t => H i (Real.exp t)) hH (by
      intro i t
      have hb' := hB i (Real.exp t) (Real.exp_pos _)
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm t] at hb'
      exact hb')
  rw [← Real.exp_log hR, sourceThetaGaussianProfile_exp]
  unfold sourceThetaGaussianLogSmooth
  calc
    _ = ∫ y : ℝ, sourceThetaGaussianLogKernel C₀ A₀ r y *
        (∑' i : I, A i * H i (Real.exp (z + l i + (-1)*y))) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hI _ (Real.exp_pos _)]
      apply congrArg (sourceThetaGaussianLogKernel C₀ A₀ r y * ·)
      apply tsum_congr
      intro i
      change A i * H i (L i.1.val * Real.exp (z + (-1)*y)) =
        A i * H i (Real.exp (z + l i + (-1)*y))
      apply congrArg (fun t : ℝ => A i * H i t)
      rw [show z + l i + (-1)*y = l i + (z + (-1)*y) by ring,
        Real.exp_add (l i) (z + (-1)*y), hl i]
    _ = _ := by
      refine hsm.trans (tsum_congr ?_)
      intro i
      have hp := sourceThetaGaussianProfile_exp C₀ A₀ r (-1) (H i) (z + l i)
      rw [Real.exp_add z (l i), hl i, mul_comm (Real.exp z)] at hp
      exact congrArg (A i * ·) hp.symm

end
end ArtinMatthews.SourceEulerAssembly
