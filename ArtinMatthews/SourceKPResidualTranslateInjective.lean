module

public import ArtinMatthews.SourceKPTranslateGramSpectral
public import ArtinMatthews.SourceKPResidualHighMeanOrthogonal


set_option backward.privateInPublic true
@[expose] public section

/-! A finite relation among actual translated residual vectors vanishes
once the adjoint traces have zero high unipotent mean. -/
namespace ArtinMatthews
open NumberField MeasureTheory HilbertResolvent
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (F : Finset (SourceKPFiniteAdeleProjective K hζ))
variable {ι : Type*} [Fintype ι]
variable (t : ι → SourceKPFiniteAdeleProjective K hζ)
variable (ht : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i))
variable (c : ι → ℂ)
local notation "V" => SourceKPCompactGenuineH1 K hζ
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μF" => sourceKPTranslateCompactHaar K hζ F
local notation "P[" i "]" => sourceKPTranslateGenuinePullbackL2 K hζ F (t i) (ht i)

def sourceKPResidualTranslateCombination {T : ℝ} (hT : 2 < T) : Lp ℂ 2 μF :=
  ∑ i, c i • P[i] (sourceKPAutomorphicExceptionalResidue K hζ (by linarith : 1 ≤ T))

def sourceKPResidualTranslateTestVector {T : ℝ} (hT : 2 < T) (i : ι) : V :=
  ∑ k, c k • sourceKPTranslateGenuineGramH1 K hζ F (t i) (ht i) (t k) (ht k)
    (sourceKPAutomorphicExceptionalFormResidue K hζ (by linarith : 1 ≤ T))

theorem sourceKPResidualTranslateTestVector_mass {T : ℝ} (hT : 2 < T) (i : ι) :
    j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i) =
      (P[i]).adjoint (sourceKPResidualTranslateCombination K hζ F t ht c hT) := by
  simp only [sourceKPResidualTranslateTestVector,sourceKPResidualTranslateCombination,
    map_sum,map_smul,sourceKPTranslateGenuineGramH1_mass,
    sourceKPAutomorphicExceptionalFormResidue_mass,sourceKPTranslateGenuineGramL2,
    ContinuousLinearMap.comp_apply]

theorem sourceKPResidualTranslateTestVector_mem_null {T : ℝ} (hT : 2 < T) (i : ι) :
    sourceKPResidualTranslateTestVector K hζ F t ht c hT i ∈
      nullSpace ((j).adjoint.comp j) (exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ)) := by
  let N := nullSpace ((j).adjoint.comp j) (exceptionalCenter (InfinitePlace.nrComplexPlaces K : ℝ))
  apply N.sum_mem
  intro k _
  apply N.smul_mem
  exact sourceKPTranslateGenuineGramH1_mem_nullSpace K hζ F (t i) (ht i) (t k) (ht k) _
    (sourceKPAutomorphicExceptionalFormResidue_mem_null K hζ (by linarith : 1 ≤ T))

theorem sourceKPResidualTranslateCombination_eq_zero_of_highMean_zero
    {T : ℝ} (hT : 2 < T)
    (hmean : ∀ i, ∀ᵐ x ∂(sourceKPHighRepresentativeHaar K hζ (T/2)).restrict
        (sourceKPCuspBandHighSection K hζ (T/2)),
      sourceKPCompactHighUnipotentMean K hζ (T/2)
        ((j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val : Y → ℂ) x = 0) :
    sourceKPResidualTranslateCombination K hζ F t ht c hT = 0 := by
  let w := sourceKPResidualTranslateCombination K hζ F t ht c hT
  let R := sourceKPAutomorphicExceptionalResidue K hζ (by linarith : 1 ≤ T)
  have hi (i : ι) : inner ℂ (P[i] R) w = 0 := by
    have ho := sourceKPExceptionalResidue_inner_eq_zero_of_highMean_zero K hζ hT
      (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)
      (sourceKPResidualTranslateTestVector_mem_null K hζ F t ht c hT i) (hmean i)
    rw [sourceKPResidualTranslateTestVector_mass K hζ F t ht c hT i] at ho
    have hrev : inner ℂ R ((P[i]).adjoint w) = 0 :=
      (inner_eq_zero_symm (𝕜 := ℂ) (E := H) (x := (P[i]).adjoint w) (y := R)).mp ho
    rw [(P[i]).adjoint_inner_right R w] at hrev
    exact hrev
  apply (inner_self_eq_zero (𝕜 := ℂ) (x := w)).mp
  change inner ℂ (∑ i, c i • P[i] R) w = 0
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_smul_left,hi,mul_zero]

end
end ArtinMatthews
