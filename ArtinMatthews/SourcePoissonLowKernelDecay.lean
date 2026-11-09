module

public import ArtinMatthews.SourcePoissonGoodHeightMajorants


set_option backward.privateInPublic true
@[expose] public section

/-! The low-w row kernel has arbitrary decay in the actual z weight.
The xi reciprocal is kept explicit so that the same estimate applies
on the finite good box and on the original right tail. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "K" => sourceContinuedPoissonRowKernel F S₀ hζ η hJ
local notation "Cw" => (3/1000 : ℝ)
local notation "Cz" => (2/5 : ℝ)

omit [IsTotallyComplex F] in
theorem exists_sourcePoissonLowContourWeights_height_decay (v : InfinitePlace F) (m n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ y t : ℝ,
      ((|y|+2)^m*‖sourceProbeW1Mellin (sourcePoissonVertical Cw y)‖)*
        ‖sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical Cz t)‖ ≤
        D*sourceContourHeightWeight y/(1+|t|)^(n+2) := by
  obtain ⟨C, hC, hw⟩ := sourceProbeW1Mellin_strip_decay Cw Cw (m+2)
  obtain ⟨B, hB, hm⟩ := sourceSLocalProbeMellin_vertical_rapid F hζ S v (n+2) Cz Cz (by norm_num)
  refine ⟨((2 : ℝ)^m*C)*(B+1), by positivity, ?_⟩
  intro y t
  have hW := hw (sourcePoissonVertical Cw y) (by rw [sourcePoissonVertical_re]) (by rw [sourcePoissonVertical_re])
  rw [sourcePoissonVertical_im] at hW
  have hW' := sourceContourHeightWeight_of_rapid m y C _ (norm_nonneg _) hW
  have hM := hm (sourcePoissonVertical Cz t) (by rw [sourcePoissonVertical_re]) (by rw [sourcePoissonVertical_re])
  rw [sourcePoissonVertical_im, mul_comm] at hM
  have hM' := (le_div_iff₀ (by positivity : 0 < (1+|t|)^(n+2))).mpr (hM.trans (le_add_of_nonneg_right zero_le_one))
  exact (mul_le_mul hW' hM' (norm_nonneg _)
    (mul_nonneg (by positivity) (sourceContourHeightWeight_nonneg y))).trans_eq (by ring)

theorem exists_sourceContinuedPoissonLowKernel_decay
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (u : {a : R // a ≠ 0}), (¬ ∃ x : F, x^6 = (u.val : F)) →
      ∀ U : ℝ, 0 < U → U ≤ sourcePoissonFrequencyNorm F S₀ u → sourcePoissonFrequencyNorm F S₀ u ≤ 2*U →
      ∀ Z : ℝ, 0 < Z → ∀ a : ℝ, (499/500 : ℝ) ≤ a → ∀ y t x : ℝ,
      ‖K v u (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z
          (sourcePoissonVertical a x,sourcePoissonVertical Cw y,sourcePoissonVertical Cz t)‖ ≤
        (D*Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)*U^(1/10+ε)*
          ‖sourceRowTwistReciprocal F hζ S₀ u.val u.property η hJ (sourcePoissonVertical a x)‖)*
          (sourceContourHeightWeight y*(Real.exp (-((x+t)^2))/(1+|t|)^(n+2))) := by
  obtain ⟨m, h⟩ := exists_sourceRowEulerContinuation_dyadic_low_w_bound F hζ S₀ η hJ hcut Cz (by norm_num)
  obtain ⟨C, hC, hA⟩ := h ε hε
  obtain ⟨D, hD, hW⟩ := exists_sourcePoissonLowContourWeights_height_decay F S₀ hζ v m n
  refine ⟨C*D, mul_pos hC hD, ?_⟩
  intro u hu U hU hUq hqU Z hZ a ha y t x
  let X := Z^(9/10 : ℝ)
  let Y := Z^(133/1000 : ℝ)
  let q : ProbeCoordinates := (sourcePoissonVertical a x,sourcePoissonVertical Cw y,sourcePoissonVertical Cz t)
  have hξ : q.1.re = a := sourcePoissonVertical_re _ _
  have hw : q.2.1.re = Cw := sourcePoissonVertical_re _ _
  have hz : q.2.2.re = Cz := sourcePoissonVertical_re _ _
  have hp : q ∈ probeEulerDomain := Or.inl ⟨by rw [hξ]; linarith, by rw [hw]; norm_num, by rw [hz]; norm_num⟩
  have hq := sourcePoissonFrequencyNorm_eq_exterior F S₀ hζ u
  rw [hq] at hUq hqU
  have H := hA u.val u.property hu U hU hUq hqU q hp hw.ge hz.ge
  rw [← Complex.ofReal_natCast, ← hq, hz, show (1/2 : ℝ)-Cz+ε = 1/10+ε by ring] at H
  have hWim : q.2.1.im = y := sourcePoissonVertical_im _ _
  rw [hWim] at H
  have hscale := sourcePoissonTripleScale_source_scales hZ a Cw Cz
  change ‖K v u X Y Z q‖ ≤ _
  have hnorm := sourceContinuedPoissonRowKernel_vertical_norm F S₀ hζ η hJ v u
    (Real.rpow_pos_of_pos hZ (9/10)) (Real.rpow_pos_of_pos hZ (133/1000)) hZ a Cw Cz ((y,t),x)
  change ‖K v u X Y Z q‖ = _ at hnorm
  rw [hnorm]
  change (sourcePoissonTripleScale (Z^(9/10 : ℝ)) (Z^(133/1000 : ℝ)) Z a Cw Cz * _) * _ ≤ _
  rw [hscale]
  let E := Z^(sourceContourExponent a Cw Cz)*Real.exp ((a+Cz-1)^2)
  let T := ‖sourceRowTwistReciprocal F hζ S₀ u.val u.property η hJ (sourcePoissonVertical a x)‖
  let W := ‖sourceProbeW1Mellin (sourcePoissonVertical Cw y)‖
  let M := ‖sourceSLocalProbeMellin F hζ S v (sourcePoissonVertical Cz t)‖
  let G := Real.exp (-((x+t)^2))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  calc
    _ ≤ (E*(C*U^(1/10+ε)*(|y|+2)^m*T))*((W*M)*G) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H hE) (by dsimp [W,M,G]; positivity)
    _ = (E*C*U^(1/10+ε)*T)*(((|y|+2)^m*W)*M)*G := by ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hW y t) (by dsimp [T]; positivity : 0 ≤ E*C*U^(1/10+ε)*T))
        (Real.exp_nonneg (-((x+t)^2)))
      exact h.trans_eq (by dsimp only [E,T,G]; rw [div_eq_mul_inv, div_eq_mul_inv]; ring)

end
end ArtinMatthews.SourceEulerAssembly
