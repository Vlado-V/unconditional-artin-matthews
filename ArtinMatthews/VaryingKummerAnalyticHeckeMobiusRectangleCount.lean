module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusClassPolynomial
public import ArtinMatthews.VaryingKummerAnalyticHeckeRectangleSieve


set_option backward.privateInPublic true
@[expose] public section

/-! A real zero-detection counting input: the actual smoothed Mobius
polynomial, anywhere in a rectangle, with its square mass derived from
ideal norms. No large-value or coefficient-mass assumption is supplied. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Complex Set
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem exists_actual_mobius_smoothed_rectangle_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D Y σ₀ σ₁ X U H Z δ : ℝ),
      0 < Y → σ₀ ≤ σ₁ → 1 ≤ X → 1 ≤ U → 0 ≤ H → 0 < Z → 0 < δ → 1+3*ε ≤ 2*σ₀ →
      ∀ (T : Finset (IdealConductorModulus K))
        (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
        (B : ∀ c : ClassGroup (𝓞 K),
          Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c))),
        (∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U) →
        (∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue) →
        (∀ c, ∀ J ∈ B c, Z ≤ (FractionalIdeal.absNorm J.val.val : ℝ)) →
        (∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X) →
        (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
          (fun a => ∃ σ t : ℝ, σ ∈ Icc σ₀ σ₁ ∧ |t| ≤ H ∧
            δ ≤ ‖coefficientClassDirichletPolynomial K a B (mobiusSmoothedClassWeight K D Y) σ t‖)).card : ℝ) ≤
          C*(1+2*(σ₁-σ₀))*(1+4*H)*(X+U^2)*(1+(Real.log X)^2)^2*
            Z^(1+3*ε-2*σ₀)/δ^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_mobiusClassWeight_mass_bound K ε hε
  let A₀ : ℝ := (NumberField.classNumber K : ℝ)*heckeConductorClassConstant K
  have hA₀ : 0 < A₀ := by
    have hc := heckeConductorClassConstant_pos K
    have hclass : 0 < (NumberField.classNumber K : ℝ) := by exact_mod_cast NumberField.classNumber_pos K
    exact mul_pos hclass hc
  refine ⟨A₀*C,mul_pos hA₀ hC,?_⟩
  intro D Y σ₀ σ₁ X U H Z δ hY hσ hX hU hH hZ hδ he T A B hT hA hB hB'
  have Hrect := actualHecke_coefficientFamily_rectangle_count K hU hX hσ hH T hT A hA B hB'
    (mobiusSmoothedClassWeight K D Y) δ hδ
  have hm := (mobiusSmoothedClassWeight_mass_le K D Y σ₀ hY B).trans
    (hbound D σ₀ Z B hZ he hB)
  let fac : ℝ := (1+2*(σ₁-σ₀))*(1+4*H)*A₀*(X+U^2)*(1+(Real.log X)^2)^2/δ^2
  have hfac : 0 ≤ fac := by
    have hw : 0 ≤ 1+2*(σ₁-σ₀) := by linarith
    dsimp [fac]
    positivity
  apply Hrect.trans
  convert mul_le_mul_of_nonneg_left hm hfac using 1 <;> dsimp [fac,A₀] <;> ring

end
end ArtinMatthews.VaryingKummerAnalytic
