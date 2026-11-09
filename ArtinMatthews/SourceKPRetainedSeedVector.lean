module

public import ArtinMatthews.SourceKPRetainedPositiveSeed
public import ArtinMatthews.SourceKPCuspResidualFourierRelation


set_option backward.privateInPublic true
@[expose] public section

/-! The retained positive average is a nonzero vector in the actual
common-level residual span, on the original retained support. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic SourcePhysical SourceReflection
open QuadraticWeil MeasureTheory
open scoped NumberField MatrixGroups AdeleRing SourcePhysical Classical BigOperators NNReal ENNReal

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (R M : S → ℕ)

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "A" => SourceKPRetainedSeedIndex K S R M
local notation "t" => sourceKPRetainedSeedTranslate K hζ S R M

def sourceKPRetainedSeedLevel (qf : Gf) : Finset Gf :=
  Finset.univ.image (t qf)

local notation "F" => sourceKPRetainedSeedLevel K hζ S R M

theorem sourceKPRetainedSeedLevel_le_conjugate (qf : Gf) (a : A) :
    sourceKPFiniteTranslateLevel K hζ (F qf) ≤
      sourceKPFiniteLevelConjugate K hζ (t qf a) :=
  sourceKPFiniteTranslateLevel_le_conjugate K hζ (F qf)
    (Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩)

local notation "ht" => sourceKPRetainedSeedLevel_le_conjugate K hζ S R M

def sourceKPRetainedSeedVector {T : ℝ} (hT : 2 < T) (qf : Gf) :
    Lp ℂ 2 (sourceKPTranslateCompactHaar K hζ (F qf)) :=
  sourceKPResidualTranslateCombination K hζ (F qf) (t qf) (ht qf)
    (sourceKPRetainedSeedWeight K S R M) hT

theorem sourceKPRetainedSeedVector_coe {T : ℝ} (hT : 2 < T) (qf : Gf) :
    (sourceKPRetainedSeedVector K hζ S R M hT qf :
      SourceKPTranslateAutomorphicCompactLevel K hζ (F qf) → ℂ) =ᵐ[
        sourceKPTranslateCompactHaar K hζ (F qf)] fun y =>
      ∑ a : A, sourceKPRetainedSeedWeight K S R M a *
        (sourceKPAutomorphicExceptionalResidue K hζ (one_le_two.trans hT.le)).val
          (sourceKPTranslateAutomorphicCompactMap K hζ (F qf) (t qf a) (ht qf a) y) :=
  sourceKPResidualTranslateCombination_coe K hζ (F qf) (t qf) (ht qf)
    (sourceKPRetainedSeedWeight K S R M) hT

theorem sourceKPRetainedPositiveSeed_exists_vector
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {T : ℝ} (hT : 2 < T) :
    let S := sourceHilbertSet K S₀
    ∃ (a : GL (Fin 2) 𝔸ᶠ[K]) (R M : S → ℕ)
      (U : ∀ P : S, SourceThetaFiniteCutoff K P.val),
      let q₀ := (sourceKPAdelicRootSupportTuple K hζ 1 a S).2
      let C := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
      C q₀ ≠ 0 ∧ sourceKPRetainedSeedVector K hζ S R M hT q₀ ≠ 0 ∧
      ∀ z : ∀ P : S, (P.val.adicCompletion K)ˣ,
        sourceKPRetainedSeedCoefficient K hζ S R M (one_le_two.trans hT.le) q₀ z =
          C q₀ * ∏ P : S, (U P).factor (z P) := by
  let S := sourceHilbertSet K S₀
  obtain ⟨a,R,M,U,hne,hEq⟩ := sourceKPRetainedPositiveSeed_exists K hζ S₀ hS hT
  refine ⟨a,R,M,U,hne,?_,hEq⟩
  intro hzero
  let q₀ := (sourceKPAdelicRootSupportTuple K hζ 1 a S).2
  let z : ∀ P : S, (P.val.adicCompletion K)ˣ := fun _ => 1
  have hz := hEq z
  have hfac (P : S) : (U P).factor (z P) = 1 :=
    Set.indicator_of_mem (U P).one_mem _
  simp only [hfac, Finset.prod_const_one, mul_one] at hz
  have hC : sourceKPRetainedSeedCoefficient K hζ S R M (one_le_two.trans hT.le) q₀ z = 0 :=
    sourceKPCuspResidualFourierValue_sum_eq_zero_of_translateCombination K hζ
      (sourceKPRetainedSeedLevel K hζ S R M q₀)
      (sourceKPRetainedSeedTranslate K hζ S R M q₀)
      (sourceKPRetainedSeedLevel_le_conjugate K hζ S R M q₀)
      (sourceKPRetainedSeedWeight K S R M) hT hzero 1
      (D (sourceKPRetainedDiagonalUnit K S z))
  exact hne (hz.symm.trans hC)

end
end ArtinMatthews
