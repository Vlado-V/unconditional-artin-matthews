module

public import ArtinMatthews.VaryingKummerAnalyticHeckePrimitiveZeroDensity
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveGoodReciprocal


set_option backward.privateInPublic true
@[expose] public section

/-! An actual exceptional family and the reciprocal bound on its
complement. The zero-free rectangle used in local logarithmic control is
proved from nonmembership in this explicit finite exceptional set. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def primitiveExceptionalCoefficients (M : IdealConductorModulus K)
    (A : Finset (EvenIdealRayCharacter K M.val)) (U r : ℝ) :
    Finset (integralFractionalIdeals K → ℂ) :=
  (A.image (fun ψ => ψ.coefficient)).filter (primitiveZeroCoefficient K M A U r)

theorem primitiveExceptionalCoefficients_complement_nonvanishing
    (M : IdealConductorModulus K) (A : Finset (EvenIdealRayCharacter K M.val)) (U r : ℝ)
    (ψ : EvenIdealRayCharacter K M.val) (hψ : ψ ∈ A)
    (hprim : IsPrimitiveOnIdeals ψ.residue)
    (hgood : ψ.coefficient ∉ primitiveExceptionalCoefficients K M A U r) :
    ∀ z : ℂ, (249/250 : ℝ) ≤ z.re → |z.im| ≤ 4*U^r →
      ψ.primitiveContinued M.property hprim z ≠ 0 := by
  intro z hz him hzero
  apply hgood
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨ψ,hψ,rfl⟩,
    ψ,hψ,rfl,hprim,z,hz,him,hzero⟩

theorem exists_actual_primitive_good_family :
    ∃ r C U₀ : ℝ, 0 < r ∧ r < 1/10 ∧ 0 < C ∧ 2 ≤ U₀ ∧
      (∀ U : ℝ, U₀ ≤ U →
        ∀ (T : Finset (IdealConductorModulus K))
          (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val)),
          (∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U) →
          (∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue) →
          (∀ M ∈ T, ∀ ψ ∈ A M, ψ.IsNonprincipal) →
          (∑ M ∈ T, ((primitiveExceptionalCoefficients K M (A M) U r).card : ℝ)) ≤ C*U^(1/2 : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧
        ∀ U : ℝ, U₀ ≤ U →
        ∀ (T : Finset (IdealConductorModulus K))
          (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val)),
          (∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U) →
          (∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue) →
          (∀ M ∈ T, ∀ ψ ∈ A M, ψ.IsNonprincipal) →
          ∀ M ∈ T, ∀ ψ ∈ A M, ∀ hprim : IsPrimitiveOnIdeals ψ.residue,
            ψ.coefficient ∉ primitiveExceptionalCoefficients K M (A M) U r →
            ∀ s : ℂ, (499/500 : ℝ) ≤ s.re → |s.im| ≤ 2*U^r →
              ‖(ψ.primitiveContinued M.property hprim s)⁻¹‖ ≤ B*U^ε) := by
  obtain ⟨r,C,U₀,hr,hr',hC,hU₀,hcount⟩ := exists_actual_primitive_zero_density_half K
  refine ⟨r,C,U₀,hr,hr',hC,hU₀,hcount,?_⟩
  intro ε hε
  obtain ⟨B,hB,hrec⟩ := exists_primitive_reciprocal_bound_on_zero_free_rectangle K ε hε
  refine ⟨B,hB,?_⟩
  intro U hU T A hT _hA hnp M hMT ψ hψ hprim hgood s hs him
  apply hrec U r (by linarith [hU₀.trans hU]) hr hr' ψ M.property hprim
    (hnp M hMT ψ hψ) (hT M hMT)
    (primitiveExceptionalCoefficients_complement_nonvanishing K M (A M) U r ψ hψ hprim hgood) s hs him

end
end ArtinMatthews.VaryingKummerAnalytic
