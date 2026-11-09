module

public import ArtinMatthews.SourceKPResidualTranslateInjective
public import ArtinMatthews.SourceKPTranslateTraceAEAlgebra


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nullspace test vector is represented by the literal
adjoint trace of the common-level residual combination. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

private theorem lp_sum_smul_coe {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (f : ι → Lp ℂ 2 μ) :
    ((∑ i, c i • f i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
      fun x => ∑ i, c i * f i x := by
  apply (Lp.coeFn_finsetSum Finset.univ (fun i => c i • f i)).trans
  have he : ∀ᵐ x ∂μ, ∀ i, ((c i • f i : Lp ℂ 2 μ) : X → ℂ) x = c i * f i x := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (f i)] with x hx
    exact hx
  filter_upwards [he] with x hx
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hx i)

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (F : Finset (SourceKPFiniteAdeleProjective K hζ))
variable {ι : Type*} [Fintype ι]
variable (t : ι → SourceKPFiniteAdeleProjective K hζ)
variable (ht : ∀ i, sourceKPFiniteTranslateLevel K hζ F ≤ sourceKPFiniteLevelConjugate K hζ (t i))
variable (c : ι → ℂ)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ F
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μJ" => sourceKPTranslateCompactHaar K hζ F
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "P[" i "]" => sourceKPTranslateGenuinePullbackL2 K hζ F (t i) (ht i)
local notation "Tr[" i "]" => sourceKPTranslateCompactTrace K hζ F (t i) (ht i)

theorem sourceKPResidualTranslateTestVector_trace_ae
    {T : ℝ} (hT : 2 < T) (i : ι) :
    ((j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val : Y → ℂ) =ᵐ[μY]
      Tr[i] (sourceKPResidualTranslateCombination K hζ F t ht c hT : YJ → ℂ) := by
  let R := sourceKPAutomorphicExceptionalResidue K hζ (by linarith : 1 ≤ T)
  let w := sourceKPResidualTranslateCombination K hζ F t ht c hT
  let A (k : ι) := sourceKPTranslateGenuineGramL2 K hζ F (t i) (ht i) (t k) (ht k) R
  let L : H →ₗ[ℂ] Lp ℂ 2 μY :=
    (sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)).subtype
  have hmass : (j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val =
      ∑ k, c k • (A k).val := by
    change L (j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)) = ∑ k, c k • L (A k)
    simp only [sourceKPResidualTranslateTestVector,map_sum,map_smul,
      sourceKPTranslateGenuineGramH1_mass,sourceKPAutomorphicExceptionalFormResidue_mass,A,R]
  have hleft : ((j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val : Y → ℂ) =ᵐ[μY]
      fun y => ∑ k, c k * (A k).val y := by
    rw [hmass]
    exact lp_sum_smul_coe c (fun k => (A k).val)
  have hG (k : ι) : ((A k).val : Y → ℂ) =ᵐ[μY] Tr[i] (P[k] R : YJ → ℂ) :=
    sourceKPTranslateGenuineGramL2_trace_pullback_ae K hζ F (t i) (ht i) (t k) (ht k) R
  have hleft' : ((j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val : Y → ℂ) =ᵐ[μY]
      fun y => ∑ k, c k * Tr[i] (P[k] R : YJ → ℂ) y := by
    apply hleft.trans
    filter_upwards [ae_all_iff.mpr hG] with y hy
    exact Finset.sum_congr rfl (fun k _ => congrArg (fun z : ℂ => c k*z) (hy k))
  have hw : (w : YJ → ℂ) =ᵐ[μJ] fun x => ∑ k, c k * P[k] R x :=
    lp_sum_smul_coe c (fun k => P[k] R)
  have htrace := sourceKPTranslateCompactTrace_congr_ae K hζ F (t i) (ht i) hw
  have hlin : Tr[i] (fun x => ∑ k, c k * P[k] R x) =
      fun y => ∑ k, c k * Tr[i] (P[k] R : YJ → ℂ) y := by
    funext y
    obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    rw [sourceKPTranslateCompactTrace_upper]
    simp_rw [sourceKPTranslateCompactTrace_upper,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hlin] at htrace
  exact hleft'.trans htrace.symm

theorem sourceKPResidualTranslateTestVector_trace_ae_of_ae
    {T : ℝ} (hT : 2 < T) (i : ι) (v : YJ → ℂ)
    (hv : (sourceKPResidualTranslateCombination K hζ F t ht c hT : YJ → ℂ) =ᵐ[μJ] v) :
    ((j (sourceKPResidualTranslateTestVector K hζ F t ht c hT i)).val : Y → ℂ) =ᵐ[μY] Tr[i] v :=
  (sourceKPResidualTranslateTestVector_trace_ae K hζ F t ht c hT i).trans
    (sourceKPTranslateCompactTrace_congr_ae K hζ F (t i) (ht i) hv)

end
end ArtinMatthews
