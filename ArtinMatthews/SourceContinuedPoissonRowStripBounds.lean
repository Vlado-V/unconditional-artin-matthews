module

public import ArtinMatthews.SourceContinuedPoissonRowKernel
public import ArtinMatthews.SourceContourHeightWeight


set_option backward.privateInPublic true
@[expose] public section

/-! A uniform height majorant on each fixed right-hand real box for the
literal nonprincipal row. The Gaussian decays in `Im(ξ)+Im(z)`, and
both actual Mellin weights supply their own inverse quadratic factors. -/
namespace ArtinMatthews.SourcePhysical
open Set
noncomputable section

theorem sourcePoissonTripleScale_bounded_on_box {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc a₀ a₁, ∀ b ∈ Icc b₀ b₁, ∀ c ∈ Icc c₀ c₁,
      sourcePoissonTripleScale X Y Z a b c ≤ C := by
  let K : Set (ℝ × ℝ × ℝ) := Icc a₀ a₁ ×ˢ (Icc b₀ b₁ ×ˢ Icc c₀ c₁)
  let A : ℝ × ℝ × ℝ → ℝ := fun p => sourcePoissonTripleScale X Y Z p.1 p.2.1 p.2.2
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hA : Continuous A := by
    simp_rw [A, sourcePoissonTripleScale, Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hY,
      Real.rpow_def_of_pos hZ]
    fun_prop
  obtain ⟨C, hC⟩ := hK.bddAbove_image hA.continuousOn
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro a ha b hb c hc
  exact (hC (show A (a,b,c) ∈ A '' K from ⟨(a,b,c), ⟨ha,hb,hc⟩, rfl⟩)).trans (le_max_right _ _)

end
end ArtinMatthews.SourcePhysical

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators Set
open VaryingKummerAnalytic SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

omit [IsTotallyComplex F] in
include hζ in
theorem sourcePoissonFrequencyNorm_ge_one (u : {a : R // a ≠ 0}) :
    1 ≤ sourcePoissonFrequencyNorm F S₀ u := by
  change 1 ≤ fieldSNorm F S (sourceRowFieldUnit F S₀ u.val u.property)
  rw [sourceRowFieldNorm_eq_frequencyNorm F S₀ hζ u.val u.property]
  exact_mod_cast sourcePrimeExponentNorm_pos F S₀ (sourceElementExponents F S₀ u.val u.property)

theorem exists_sourceContinuedPoissonRowKernel_right_strip_bound
    (hcut : principalAngularCutoff F J ⊆ S) (v : InfinitePlace F) (u : {a : R // a ≠ 0})
    (hu : ¬ ∃ a : F, a^6 = (u.val : F))
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (a₀ a₁ b₁ c₁ : ℝ) (ha₀ : 1 < a₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc a₀ a₁, ∀ b ∈ Icc (3/1000 : ℝ) b₁, ∀ c ∈ Icc (2/5 : ℝ) c₁,
      ∀ (y t x : ℝ),
      ‖sourceContinuedPoissonRowKernel F S₀ hζ η hJ v u X Y Z
        (sourcePoissonVertical a x, sourcePoissonVertical b y, sourcePoissonVertical c t)‖ ≤
        C*(sourceContourHeightWeight y*sourceContourHeightWeight t)*Real.exp (-((x+t)^2)) := by
  obtain ⟨B, hB, hbnd⟩ := sourcePoissonTripleScale_bounded_on_box hX hY hZ a₀ a₁ (3/1000) b₁ (2/5) c₁
  obtain ⟨m, h⟩ := exists_sourceRowEulerContinuation_low_w_bound F hζ S₀ η hJ hcut (2/5) (by norm_num)
  obtain ⟨D, hD, hrow⟩ := h 1 (by norm_num)
  obtain ⟨B₁, hB₁, hwgt⟩ := sourceProbeW1Mellin_strip_decay (3/1000) b₁ (m+2)
  obtain ⟨B₀, hB₀, hmell⟩ := sourceSLocalProbeMellin_vertical_rapid F hζ S v 2 (2/5) c₁ (by norm_num)
  let Q : ℝ := sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ u.val u.property)
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast sourcePrimeExponentNorm_pos F S₀ (sourceElementExponents F S₀ u.val u.property)
  let Rξ := sourceRayAbsoluteEulerBound F a₀
  have hRξ : 0 < Rξ := sourceRayAbsoluteEulerBound_pos F a₀
  refine ⟨(B*D*Q^(1/2+(1:ℝ))*Rξ)*(((2 : ℝ)^m*B₁)*(B₀+1)), by positivity, ?_⟩
  intro a ha b hb c hc y t x
  let ξ := sourcePoissonVertical a x
  let w := sourcePoissonVertical b y
  let z := sourcePoissonVertical c t
  have hξ : a₀ ≤ ξ.re := by simpa only [ξ, sourcePoissonVertical_re] using ha.1
  have hw : (3/1000 : ℝ) ≤ w.re := by simpa only [w, sourcePoissonVertical_re] using hb.1
  have hz : (2/5 : ℝ) ≤ z.re := by simpa only [z, sourcePoissonVertical_re] using hc.1
  have hreg : (ξ,w,z) ∈ probeEulerDomain :=
    Or.inl ⟨by dsimp; linarith, by dsimp; linarith, by dsimp; linarith⟩
  have hR := sourceRowTwistReciprocal_norm_le_right F hζ S₀ η hJ u.val u.property ha₀ hξ
  have hA := hrow u.val u.property hu (ξ,w,z) hreg hw hz
  have hq : ‖(sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (sourcePoissonFrequencyNorm_pos F S₀ u), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (sourcePoissonFrequencyNorm_ge_one F S₀ hζ u) (by linarith)
  have hF : ‖(sourcePoissonFrequencyNorm F S₀ u : ℂ)^(-z)*
        sourceRowEulerContinuation F hζ S₀ u.val u.property η hJ (ξ,w,z)‖ ≤
      D*Q^(1/2+(1:ℝ))*(|y|+2)^m*Rξ := by
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hq).trans
    have H := hA.trans (mul_le_mul_of_nonneg_left hR (by positivity))
    simpa only [w, sourcePoissonVertical_im] using H
  have hW : (|y|+2)^m*‖sourceProbeW1Mellin w‖ ≤
      ((2 : ℝ)^m*B₁)*sourceContourHeightWeight y := by
    apply sourceContourHeightWeight_of_rapid m y B₁ _ (norm_nonneg _)
    simpa only [w, sourcePoissonVertical_im] using hwgt w hw (by simpa only [w, sourcePoissonVertical_re] using hb.2)
  have hM : ‖sourceSLocalProbeMellin F hζ S v z‖ ≤ (B₀+1)*sourceContourHeightWeight t := by
    have H := sourceContourHeightWeight_of_rapid 0 t B₀ _ (norm_nonneg _)
      (by simpa only [z, sourcePoissonVertical_im] using hmell z hz (by simpa only [z, sourcePoissonVertical_re] using hc.2))
    simp only [pow_zero, one_mul] at H
    exact H.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (sourceContourHeightWeight_nonneg t))
  have hnorm := sourceContinuedPoissonRowKernel_vertical_norm F S₀ hζ η hJ v u hX hY hZ a b c ((y,t),x)
  dsimp only at hnorm
  change ‖sourceContinuedPoissonRowKernel F S₀ hζ η hJ v u X Y Z (ξ,w,z)‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ (B*(D*Q^(1/2+(1:ℝ))*(|y|+2)^m*Rξ))*
        ((‖sourceProbeW1Mellin w‖*‖sourceSLocalProbeMellin F hζ S v z‖)*Real.exp (-((x+t)^2))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hbnd a ha b hb c hc) hF (norm_nonneg _) hB.le) (by positivity)
    _ = (B*D*Q^(1/2+(1:ℝ))*Rξ)*
        (((|y|+2)^m*‖sourceProbeW1Mellin w‖)*‖sourceSLocalProbeMellin F hζ S v z‖)*Real.exp (-((x+t)^2)) := by ring
    _ ≤ _ := by
      have h := mul_le_mul hW hM (norm_nonneg _)
        (mul_nonneg (by positivity) (sourceContourHeightWeight_nonneg y))
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity :
        0 ≤ B*D*Q^(1/2+(1:ℝ))*Rξ)) (Real.exp_nonneg (-((x+t)^2)))
      exact hh.trans_eq (by ring)

end
end ArtinMatthews.SourceEulerAssembly
