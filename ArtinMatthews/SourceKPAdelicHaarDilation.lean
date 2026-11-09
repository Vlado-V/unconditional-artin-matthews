module

public import ArtinMatthews.SourceKPFiniteHaarDilation
public import ArtinMatthews.SourceKPArchHaarDilation
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual trace-normalized additive adelic measure scales by the
full idele absolute norm, with both of its proven local contributions. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local notation "A" => 𝔸[K]
local notation "X" => mixedEmbedding.mixedSpace K
local notation "Y" => 𝔸ᶠ[K]
local notation "I" => IdeleGroup (𝓞 K) K
local notation "N" => sourceKPIdeleAbsoluteNorm K
local notation "E" => sourceKPAdelicMixedAddEquiv K
local notation "M₀" => sourceKPAdelicStandardHaar K

local instance sourceKPAdelicHaarDilationMeasurable : MeasurableSpace A := borel A
local instance sourceKPAdelicHaarDilationBorel : BorelSpace A := ⟨rfl⟩
local instance sourceKPAdelicHaarDilationFiniteMeasurable : MeasurableSpace Y := borel Y
local instance sourceKPAdelicHaarDilationFiniteBorel : BorelSpace Y := ⟨rfl⟩

theorem sourceKPAdelicHaarMul_mixed (a : I) (p : X × Y) :
    (a : A) * (E).symm p = (E).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace K (sourceKPIdeleInfiniteUnit K a : InfiniteAdeleRing K)*p.1,
        (sourceKPIdeleFiniteUnit K a : Y)*p.2) := by
  let e : A ≃+* (X × Y) := RingEquiv.prodCongr
    (InfiniteAdeleRing.ringEquiv_mixedSpace K) (RingEquiv.refl Y)
  apply e.injective
  change e ((a : A)*e.symm p) = e (e.symm _)
  rw [map_mul,e.apply_symm_apply,e.apply_symm_apply]
  rfl

theorem sourceKPAdelicHaar_map_mul (a : I) :
    (M₀).map (fun x : A => (a : A)*x) = ENNReal.ofReal (N a⁻¹) • M₀ := by
  let μ := sourceKPArchStandardHaar K
  let ν := sourceKPFiniteStandardHaar K
  let e : X × Y → A := (E).symm
  let u := sourceKPIdeleInfiniteUnit K a
  let v := sourceKPIdeleFiniteUnit K a
  let f : X → X := fun x => InfiniteAdeleRing.ringEquiv_mixedSpace K (u : InfiniteAdeleRing K)*x
  let g : Y → Y := fun x => (v : Y)*x
  let m : A → A := fun x => (a : A)*x
  have hf : Measurable f := (continuous_const.mul continuous_id).measurable
  have hg : Measurable g := (continuous_const.mul continuous_id).measurable
  have hm : Measurable m := (continuous_const.mul continuous_id).measurable
  have he : Measurable e := (sourceKPAdelicMixedAddEquiv_symm_continuous K).measurable
  have hc : m ∘ e = e ∘ Prod.map f g := funext (sourceKPAdelicHaarMul_mixed K a)
  calc
    _ = (μ.prod ν).map (m ∘ e) := by
      rw [sourceKPAdelicStandardHaar,Measure.map_map hm he]
    _ = ((μ.map f).prod (ν.map g)).map e := by
      rw [hc,← Measure.map_map he (hf.prodMap hg),← Measure.map_prod_map μ ν hf hg]
    _ = _ := by
      have h₁ : μ.map f = ENNReal.ofReal ‖((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ • μ :=
        sourceKPArchHaar_map_mul K u
      have h₂ : ν.map g = ENNReal.ofReal ‖((v⁻¹ : Yˣ) : Y)‖ • ν := sourceKPFiniteHaar_map_mul K v
      rw [h₁,h₂,Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
        Measure.map_smul _ he.aemeasurable]
      have hn : N a⁻¹ = ‖((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ * ‖((v⁻¹ : Yˣ) : Y)‖ := by
        change ‖(sourceKPIdeleInfiniteUnit K a⁻¹ : InfiniteAdeleRing K)‖ *
          ‖(sourceKPIdeleFiniteUnit K a⁻¹ : Y)‖ = _
        rw [map_inv,map_inv]
      have hprod : ENNReal.ofReal (N a⁻¹) =
          ENNReal.ofReal ‖((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ *
            ENNReal.ofReal ‖((v⁻¹ : Yˣ) : Y)‖ :=
        (congrArg ENNReal.ofReal hn).trans
          (ENNReal.ofReal_mul (sourceKPInfiniteUnit_norm_pos K u⁻¹).le)
      rw [hprod] <;> rfl

theorem sourceKPAdelicHaar_integral_inv_mul (a : I) (f : A → ℂ) :
    (∫ x, f (((a⁻¹ : I) : A)*x) ∂M₀) = (N a : ℂ) * ∫ x, f x ∂M₀ := by
  let e : A ≃ₜ+ A := ContinuousAddEquiv.mulLeft a⁻¹
  have hm : (M₀).map e = ENNReal.ofReal (N a) • M₀ := by
    change (M₀).map (fun x : A => ((a⁻¹ : I) : A)*x) = _
    rw [sourceKPAdelicHaar_map_mul K a⁻¹,inv_inv]
  have he := (integral_map_equiv (μ := M₀) e.toHomeomorph.toMeasurableEquiv f).symm
  change (∫ x, f (e x) ∂M₀) = ∫ x, f x ∂(M₀).map e at he
  rw [hm,integral_smul_measure,ENNReal.toReal_ofReal (sourceKPIdeleAbsoluteNorm_pos K a).le,
    Complex.real_smul] at he
  exact he

theorem sourceKPAdelicTraceHaar_integral_inv_mul {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (a : I) (f : A → ℂ) :
    (∫ x, f (((a⁻¹ : I) : A)*x) ∂sourceKPAdelicTraceProduct K) =
      (N a : ℂ) * ∫ x, f x ∂sourceKPAdelicTraceProduct K := by
  rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
  exact sourceKPAdelicHaar_integral_inv_mul K a f

end
end ArtinMatthews
