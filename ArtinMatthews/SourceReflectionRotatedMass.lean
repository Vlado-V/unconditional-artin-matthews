module

public import ArtinMatthews.SourceThetaRotatedSheetMass
public import ArtinMatthews.SourceReflectionDirichletMajorant


set_option backward.privateInPublic true
@[expose] public section

/-! The countable reflected frequency family has finite total absolute
mass on the full norm-one Haar sheet before quotient periodization. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators MeasureTheory SourceReflection SourcePhysical
open scoped NumberField ENNReal BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (v : InfinitePlace F) {δ : ℝ}
local notation "Prime" => SourceExteriorPrime F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "U" => SWholeUnits F S
local notation "Y" => SNormOne F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v

variable {V : Type*}

def sourceReflectionRotatedTerm
    (D : V → SourceThetaRotatedTensor F (sourceHilbertSet F S₀) hζ v δ)
    (f : Finset (SourceExteriorPrime F S₀))
    (j : SourceReflectionTermIndex F S₀ f → V) (a : SourceReflectionTermIndex F S₀ f → ℂ)
    (w : SourceReflectionTermIndex F S₀ f → SWholeUnits F (sourceHilbertSet F S₀) → ℂ)
    (i : SourceReflectionTermIndex F S₀ f) (x : SWholeUnits F (sourceHilbertSet F S₀)) : ℂ :=
  a i * (w i x * sourceThetaSLocalTensor F (sourceHilbertSet F S₀) hζ v
    ((D (j i)).localDeriv 0) (D (j i)).retained x)

variable (D : V → SourceThetaRotatedTensor F (sourceHilbertSet F S₀) hζ v δ)
variable (f : Finset (SourceExteriorPrime F S₀))
local notation "Idx" => SourceReflectionTermIndex F S₀ f

theorem sourceReflectionRotatedTerm_scaled_measurable (j : Idx → V) (a : Idx → ℂ)
    (w : Idx → U → ℂ) (hw : ∀ i, Measurable (w i)) (i : Idx) (u : U) :
    Measurable (fun x : Y => sourceReflectionRotatedTerm F S₀ hζ v D f j a w i ((x : U) * u)) := by
  have : BorelSpace U := sourceSWholeUnits_product_borel S v
  exact measurable_const.mul
    (((hw i).comp (continuous_subtype_val.mul continuous_const).measurable).mul
      ((D (j i)).scaled_tensor_measurable 0 u))

theorem sourceReflectionRotatedTerm_totalMass_lt_top [Fintype V]
    (hδ : 0 ≤ δ) {σ : ℝ} (hσ : 1/2 < σ)
    (j : Idx → V) (a : Idx → ℂ) (ha : ∀ i, ‖a i‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i)
    (w : Idx → U → ℂ) (hw : ∀ i x, ‖w i x‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) (u : Idx → U)
    (hu : ∀ i, sLocalNorm F S (u i) =
      sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val * T) :
    (∑' i : Idx, ∫⁻ x : Y, ‖sourceReflectionRotatedTerm F S₀ hζ v D f j a w i
      ((x : U) * u i)‖ₑ ∂ν) < ⊤ := by
  classical
  have hσδ : -δ < σ := by linarith
  choose M hM hbound using fun k => (D k).scaled_tensor_mass 0 σ hσδ
  let C := ∑ k, M k
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => hM k)
  let L (i : Idx) := sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val
  have hL (i : Idx) : 0 ≤ L i := zero_le_one.trans (sourceReflectionTermLength_one_le F S₀ _ _ _)
  have hs := (sourceReflectionCoefficient_summable F S₀ f hσ a ha).mul_left (C * T^(-σ))
  refine (ENNReal.tsum_le_tsum ?_).trans_lt hs.tsum_ofReal_lt_top
  intro i
  let G (x : Y) := sourceThetaSLocalTensor F S hζ v ((D (j i)).localDeriv 0) (D (j i)).retained
    ((x : U) * u i)
  have hG : Measurable G := (D (j i)).scaled_tensor_measurable 0 (u i)
  have hC' : M (j i) ≤ C :=
    Finset.single_le_sum (fun k _ => hM k) (Finset.mem_univ _)
  have hmass : (∫⁻ x : Y, ‖G x‖ₑ ∂ν) ≤ ENNReal.ofReal (C * (L i * T)^(-σ)) := by
    have h := hbound (j i) (u i)
    rw [hu i] at h
    exact h.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg (mul_nonneg (hL i) hT.le) _)))
  calc
    _ ≤ ∫⁻ x : Y, ‖a i‖ₑ * ‖G x‖ₑ ∂ν := by
      apply lintegral_mono
      intro x
      change ‖a i * (w i ((x : U) * u i) * G x)‖ₑ ≤ ‖a i‖ₑ * ‖G x‖ₑ
      simp only [enorm_mul]
      have hw' : ‖w i ((x : U) * u i)‖ₑ ≤ 1 := by
        rw [← ofReal_norm, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hw _ _)
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left' hw') bot_le
    _ = ‖a i‖ₑ * (∫⁻ x : Y, ‖G x‖ₑ ∂ν) := lintegral_const_mul _ hG.enorm
    _ ≤ ‖a i‖ₑ * ENNReal.ofReal (C * (L i * T)^(-σ)) := mul_le_mul_of_nonneg_left hmass bot_le
    _ = ENNReal.ofReal (C * T^(-σ) * (‖a i‖ * L i^(-σ))) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), Real.mul_rpow (hL i) hT.le]
      congr 1
      ring

end
end ArtinMatthews.SourceEulerAssembly
