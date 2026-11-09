module

public import ArtinMatthews.SourceJacquetShellIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Actual high-frequency shell cancellation. A small additive
translation leaves the completed residue weight fixed and has a genuine
nontrivial standard phase; Haar invariance forces the integral to vanish. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain LocalFieldTheory QuadraticWeil MeasureTheory StandardAdelic
open scoped NumberField ValuativeRel Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))

local instance jacquetDeepAdicRelation : ValuativeRel (P.adicCompletion F) := adicRelation F P
local instance jacquetDeepAdicLocalField : IsNonarchimedeanLocalField (P.adicCompletion F) := adicLocalField F P
local instance jacquetDeepAdicMeasurable : MeasurableSpace (P.adicCompletion F) := borel (P.adicCompletion F)
local instance jacquetDeepAdicBorel : BorelSpace (P.adicCompletion F) := ⟨rfl⟩

theorem sourceJacquetWeight_translate_small (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)
    (x : P.adicCompletion F) (z : sourceJacquetIntegers F P) (hz : ‖(z : P.adicCompletion F)‖ < 1) :
    sourceJacquetWeight F P χ (x + (z : P.adicCompletion F)) = sourceJacquetWeight F P χ x := by
  have hmem : x + (z : P.adicCompletion F) ∈ sourceJacquetIntegers F P ↔
      x ∈ sourceJacquetIntegers F P := (sourceJacquetIntegers F P).add_mem_cancel_right z.property
  by_cases hx : x ∈ sourceJacquetIntegers F P
  · let a : sourceJacquetIntegers F P := ⟨x, hx⟩
    let b : sourceJacquetIntegers F P := ⟨x + (z : P.adicCompletion F), hmem.mpr hx⟩
    have h : sourceJacquetReduction F P b = sourceJacquetReduction F P a := by
      apply (sourceJacquetReduction_eq_iff F P b a).mpr
      change ‖x + (z : P.adicCompletion F) - x‖ < 1
      rwa [add_sub_cancel_left]
    exact (sourceJacquetWeight_on_integers F P χ b).trans
      ((congrArg χ h).trans (sourceJacquetWeight_on_integers F P χ a).symm)
  · have hzx := mt hmem.mp hx
    simp only [sourceJacquetWeight, dite_eq_right hzx, dite_eq_right hx]

theorem sourceJacquetShellIntegral_eq_zero_of_translation (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)
    (t : P.adicCompletion F) (z : sourceJacquetIntegers F P) (hz : ‖(z : P.adicCompletion F)‖ < 1)
    (hψ : localFiniteCharacter F P (-(t * (z : P.adicCompletion F))) ≠ 1) :
    sourceJacquetShellIntegral F P χ t = 0 := by
  let C := P.adicCompletion F
  let U := sourceJacquetIntegers F P
  let μ := sourceJacquetHaar F P
  let : μ.IsAddHaarMeasure := sourceJacquetHaar_isAddHaar F P
  let f (x : C) := sourceJacquetWeight F P χ x * localFiniteCharacter F P (-(t * x))
  let g := (U : Set C).indicator f
  have he : (U : Set C).indicator (fun x => f (x + (z : C))) = fun x => g (x + (z : C)) := by
    funext x
    have hm : x + (z : C) ∈ U ↔ x ∈ U := U.add_mem_cancel_right z.property
    by_cases hx : x ∈ U
    · simp [g, hx, hm.mpr hx]
    · simp [g, hx, mt hm.mp hx]
  have htranslate : (∫ x in (U : Set C), f (x + (z : C)) ∂μ) = (∫ x in (U : Set C), f x ∂μ) := by
    rw [← integral_indicator U.isOpen.measurableSet, he, integral_add_right_eq_self]
    exact integral_indicator U.isOpen.measurableSet
  have hpoint (x : C) : f (x + (z : C)) = f x * localFiniteCharacter F P (-(t * (z : C))) := by
    dsimp only [f]
    rw [sourceJacquetWeight_translate_small F P χ x z hz, mul_add, neg_add, AddChar.map_add_eq_mul, mul_assoc]
  simp_rw [hpoint] at htranslate
  rw [integral_mul_const] at htranslate
  change (sourceJacquetShellIntegral F P χ t) * localFiniteCharacter F P (-(t * (z : C))) =
    sourceJacquetShellIntegral F P χ t at htranslate
  by_contra h
  apply hψ
  exact mul_left_cancel₀ h (htranslate.trans (mul_one _).symm)

theorem sourceJacquetShellIntegral_deep_frequency (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)
    (u t : P.adicCompletion F)
    (hu : (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (ht : WithZero.exp (2 : ℤ) ≤ Valued.v t) (hbad : P ∉ traceBadPlaces F) :
    sourceJacquetShellIntegral F P χ t = 0 := by
  let C := P.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let ψ := localFiniteCharacter F P
  have hnot : -(u⁻¹) ∉ P.adicCompletionIntegers F := by
    change ¬ ν (-(u⁻¹)) ≤ 1
    rw [Valuation.map_neg, map_inv₀, hu]
    decide
  have hno := mt (adicConductorZero_dual F P ψ (localFiniteCharacter_conductorZero F P hbad) (-(u⁻¹))).mp hnot
  push Not at hno
  obtain ⟨a, ha, hψ⟩ := hno
  let z : C := (u⁻¹ * a) / t
  have htpos : 0 < ν t := (by decide : 0 < WithZero.exp (2 : ℤ)).trans_le ht
  have ht0 : t ≠ 0 := fun h => htpos.ne' (by rw [h, map_zero])
  have ha' : ν a ≤ 1 := ha
  have hb : ν (u⁻¹ * a) ≤ (WithZero.exp (-1 : ℤ))⁻¹ := by
    rw [map_mul, map_inv₀, hu]
    exact mul_le_of_le_one_right zero_le ha'
  have hlt : ν (u⁻¹ * a) < ν t := hb.trans_lt
    ((by decide : (WithZero.exp (-1 : ℤ))⁻¹ < WithZero.exp (2 : ℤ)).trans_le ht)
  have hzval : ν z < 1 := by
    change ν ((u⁻¹ * a) / t) < 1
    rw [map_div₀]
    exact (div_lt_one₀ htpos).mpr hlt
  have hz : ‖z‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hzval
  let zU : sourceJacquetIntegers F P := ⟨z, (adic_integer_norm F P z).mpr hz.le⟩
  apply sourceJacquetShellIntegral_eq_zero_of_translation F P χ t zU hz
  have harg : -(t * z) = -(u⁻¹) * a := by
    dsimp only [z]
    field_simp [ht0]
  exact harg.symm ▸ hψ

end
end ArtinMatthews
