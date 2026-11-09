module

public import ArtinMatthews.KummerPrimitiveConductorFamily
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusDetectorMass


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine general-field maximal and Mobius detector estimates on
the actual distinct primitive Kummer row family. All conductor placement,
primitivity and row-to-coefficient counting are proved inputs. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain FractionalIdeal VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

theorem chosenKummerPrimitiveRows_bounded_height_count {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N)
    {X Y : ℝ} (hX : 1 ≤ X) (hY : 0 ≤ Y)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (σ δ : ℝ) (hδ : 0 < δ) :
    ((Finset.univ.filter (fun i : NonprincipalIdealRowIndex S N =>
      ∃ t : ℝ, |t| ≤ Y ∧ δ ≤ ‖coefficientClassDirichletPolynomial K
        (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient B v σ t‖)).card : ℝ) ≤
      (2*Y+4)*((heckeGaussianWindowConstant K * (X+(primitiveRowConductorBudget S N)^2) *
        (1+(Real.log X)^2)*coefficientClassDirichletMass K B v σ)/δ^2) := by
  let P := fun a : integralFractionalIdeals K → ℂ =>
    ∃ t : ℝ, |t| ≤ Y ∧ δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖
  have hc : (∑ M ∈ chosenPrimitiveConductorSupport hζ S hWild hClass N,
      (((chosenPrimitiveCharactersAt hζ S hWild hClass N M).image (fun ψ => ψ.coefficient)).filter P).card : ℝ)=
      ((Finset.univ.filter (fun i => P
        (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient)).card : ℝ) := by
    exact_mod_cast chosenPrimitiveCharactersAt_filtered_count_sum hζ S hWild hClass N P
  rw [← hc]
  exact actualHecke_coefficientFamily_bounded_height_count K
    (primitiveRowConductorBudget_ge_one S N hN) hX hY
    (chosenPrimitiveConductorSupport hζ S hWild hClass N)
    (chosenPrimitiveConductorSupport_norm_le hζ S hWild hClass N)
    (chosenPrimitiveCharactersAt hζ S hWild hClass N)
    (fun M _ ψ hψ => chosenPrimitiveCharactersAt_primitive hζ S hWild hClass N M ψ hψ)
    B hB v σ δ hδ

theorem exists_chosenKummerPrimitiveRows_mobius_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
      (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
      (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ), 1 ≤ N →
      ∀ D σ X Y Z δ : ℝ, 1 ≤ X → 0 ≤ Y → 0 < Z → 0 < δ → 1+3*ε ≤ 2*σ →
      ∀ B : ∀ c : ClassGroup (𝓞 K),
        Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)),
        (∀ c, ∀ J ∈ B c, Z ≤ (FractionalIdeal.absNorm J.val.val:ℝ)) →
        (∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val:ℝ) ≤ X) →
        ((Finset.univ.filter (fun i : NonprincipalIdealRowIndex S N =>
          ∃ t : ℝ, |t| ≤ Y ∧ δ ≤ ‖coefficientClassDirichletPolynomial K
            (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient
            B (mobiusClassWeight K D) σ t‖)).card : ℝ) ≤
          C*(2*Y+4)*(X+(primitiveRowConductorBudget S N)^2)*(1+(Real.log X)^2)*
            Z^(1+3*ε-2*σ)/δ^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_mobius_detector_bounded_height_count K ε hε
  refine ⟨C,hC,?_⟩
  intro ζ hζ S hWild hClass N hN D σ X Y Z δ hX hY hZ hδ hσ B hBl hBu
  let P := fun a : integralFractionalIdeals K → ℂ =>
    ∃ t : ℝ, |t| ≤ Y ∧ δ ≤
      ‖coefficientClassDirichletPolynomial K a B (mobiusClassWeight K D) σ t‖
  have hc : (∑ M ∈ chosenPrimitiveConductorSupport hζ S hWild hClass N,
      (((chosenPrimitiveCharactersAt hζ S hWild hClass N M).image (fun ψ => ψ.coefficient)).filter P).card : ℝ)=
      ((Finset.univ.filter (fun i => P
        (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient)).card : ℝ) := by
    exact_mod_cast chosenPrimitiveCharactersAt_filtered_count_sum hζ S hWild hClass N P
  rw [← hc]
  exact hbound D σ X (primitiveRowConductorBudget S N) Y Z δ hX
    (primitiveRowConductorBudget_ge_one S N hN) hY hZ hδ hσ
    (chosenPrimitiveConductorSupport hζ S hWild hClass N)
    (chosenPrimitiveCharactersAt hζ S hWild hClass N) B
    (chosenPrimitiveConductorSupport_norm_le hζ S hWild hClass N)
    (fun M _ ψ hψ => chosenPrimitiveCharactersAt_primitive hζ S hWild hClass N M ψ hψ) hBl hBu

end
end ArtinMatthews
