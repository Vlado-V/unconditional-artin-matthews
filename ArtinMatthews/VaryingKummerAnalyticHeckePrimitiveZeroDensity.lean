module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusAnnulusCount


set_option backward.privateInPublic true
@[expose] public section

/-! Actual zero-density consequence for finite primitive nonprincipal
Hecke families over any number field. The exceptional set is defined by
zeros of the genuine continuation, not by a supplied detector premise. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Complex Set
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def primitiveZeroCoefficient (M : IdealConductorModulus K)
    (A : Finset (EvenIdealRayCharacter K M.val)) (U r : ℝ)
    (a : integralFractionalIdeals K → ℂ) : Prop :=
  ∃ ψ ∈ A, ψ.coefficient = a ∧ ∃ hprim : IsPrimitiveOnIdeals ψ.residue,
    ∃ ρ : ℂ, (249/250 : ℝ) ≤ ρ.re ∧ |ρ.im| ≤ 4*U^r ∧
      ψ.primitiveContinued M.property hprim ρ = 0

theorem exists_actual_primitive_zero_density :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      ∀ U : ℝ, U₀ ≤ U →
      ∀ (T : Finset (IdealConductorModulus K))
        (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val)),
        (∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U) →
        (∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue) →
        (∀ M ∈ T, ∀ ψ ∈ A M, ψ.IsNonprincipal) →
        (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
          (primitiveZeroCoefficient K M (A M) U r)).card : ℝ) ≤ C*U^(2/5 : ℝ) := by
  obtain ⟨r,U₀,hr,hr',hU₀,hdetect⟩ := exists_actual_zero_large_finite_mobius_polynomial K
  obtain ⟨C,hC,hcount⟩ := exists_actual_mobius_annulus_count K
  refine ⟨r,144*C,U₀,hr,hr',by positivity,hU₀,?_⟩
  intro U hU T A hT hA hnp
  have hU1 : 1 ≤ U := by linarith [hU₀.trans hU]
  let Q (j : ℕ) (a : integralFractionalIdeals K → ℂ) : Prop :=
    ∃ σ t : ℝ, σ ∈ Icc (249/250) 1 ∧ |t| ≤ 4*U^r ∧
      1/1152 ≤ ‖coefficientClassDirichletPolynomial K a
        (heckeClassNormAnnulus K (mobiusPowerBoundary U j) (mobiusPowerBoundary U (j+1)))
        (mobiusSmoothedClassWeight K (U^2) (U^10)) σ t‖
  have hcover (M : IdealConductorModulus K) (hM : M ∈ T)
      (a : integralFractionalIdeals K → ℂ) (ha : primitiveZeroCoefficient K M (A M) U r a) :
      ∃ j : ℕ, j < 144 ∧ Q j a := by
    obtain ⟨ψ,hψ,hψa,hprim,ρ,hρ,him,hz⟩ := ha
    have hnp' := hnp M hM ψ hψ
    have hlarge := hdetect U hU ψ M.property hprim hnp' (hT M hM) ρ hρ him hz
    obtain ⟨j,hj,hjlarge⟩ := ψ.exists_large_mobiusPowerAnnulus hU1 ρ hlarge
    have hρ1 : ρ.re ≤ 1 := by
      by_contra hn
      exact (ψ.primitiveContinued_ne_zero_right M.property hprim hnp' (lt_of_not_ge hn)) hz
    refine ⟨j,hj,ρ.re,ρ.im,⟨hρ,hρ1⟩,him,?_⟩
    rw [ψ.mobiusPowerAnnulus_eq_classPolynomial hU1 ρ hj,hψa] at hjlarge
    exact hjlarge
  have hcard (M : IdealConductorModulus K) (hM : M ∈ T) :
      ((((A M).image (fun ψ => ψ.coefficient)).filter
        (primitiveZeroCoefficient K M (A M) U r)).card : ℝ) ≤
      ∑ j ∈ Finset.range 144, ((((A M).image (fun ψ => ψ.coefficient)).filter (Q j)).card : ℝ) := by
    have hsub : ((A M).image (fun ψ => ψ.coefficient)).filter
        (primitiveZeroCoefficient K M (A M) U r) ⊆
        (Finset.range 144).biUnion (fun j => ((A M).image (fun ψ => ψ.coefficient)).filter (Q j)) := by
      intro a ha
      obtain ⟨j,hj,hja⟩ := hcover M hM a (Finset.mem_filter.mp ha).2
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hj,
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,hja⟩⟩
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    _ ≤ ∑ M ∈ T, ∑ j ∈ Finset.range 144,
        ((((A M).image (fun ψ => ψ.coefficient)).filter (Q j)).card : ℝ) := Finset.sum_le_sum hcard
    _ = ∑ j ∈ Finset.range 144, ∑ M ∈ T,
        ((((A M).image (fun ψ => ψ.coefficient)).filter (Q j)).card : ℝ) := Finset.sum_comm
    _ ≤ ∑ _j ∈ Finset.range 144, C*U^(2/5 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcount U hU1 r hr'.le j (Finset.mem_range.mp hj) T A hT hA
    _ = _ := by simp; ring

theorem exists_actual_primitive_zero_density_half :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      ∀ U : ℝ, U₀ ≤ U →
      ∀ (T : Finset (IdealConductorModulus K))
        (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val)),
        (∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U) →
        (∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue) →
        (∀ M ∈ T, ∀ ψ ∈ A M, ψ.IsNonprincipal) →
        (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
          (primitiveZeroCoefficient K M (A M) U r)).card : ℝ) ≤ C*U^(1/2 : ℝ) := by
  obtain ⟨r,C,U₀,hr,hr',hC,hU₀,hbound⟩ := exists_actual_primitive_zero_density K
  refine ⟨r,C,U₀,hr,hr',hC,hU₀,?_⟩
  intro U hU T A hT hA hnp
  apply (hbound U hU T A hT hA hnp).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [hU₀.trans hU]) (by norm_num)

end
end ArtinMatthews.VaryingKummerAnalytic
