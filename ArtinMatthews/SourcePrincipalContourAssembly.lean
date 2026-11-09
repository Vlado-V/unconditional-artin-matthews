module

public import ArtinMatthews.SourcePrincipalContourFubini
public import ArtinMatthews.SourcePrincipalPoleCrossings
public import ArtinMatthews.SourcePrincipalOuterShift
public import ArtinMatthews.SourcePrincipalRemainders


set_option backward.privateInPublic true
@[expose] public section

/-! The actual principal integral splits into its two contour remainders and
the normalized double residue. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory Set
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.PrincipalMellinResidues
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
variable (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
local notation "σ₁" => sourcePrincipalSigma
local notation "z₁" => sourcePrincipalZetaLine
local notation "V" => sourcePoissonVertical
local notation "N" => sourcePoissonNormalization
local notation "μ₂" => (Measure.prod (volume : Measure ℝ) (volume : Measure ℝ))

include hJ hcut in
private theorem principalOuterSlice_w {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (u : ℝ)
    (hi : Integrable (fun p : ℝ × ℝ =>
      sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z σ₁ σ₁ z₁ (p,u)) μ₂)
    (hl : Integrable (fun p : ℝ × ℝ =>
      sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z σ₁ (95 / 100) z₁ (p,u)) μ₂)
    (hr : Integrable (fun y : ℝ =>
      sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z σ₁ z₁ (y,u))) :
    sourcePrincipalPoissonOuterSlice F hζ S₀ η v X Y Z σ₁ σ₁ z₁ u =
      sourcePrincipalPoissonOuterSlice F hζ S₀ η v X Y Z σ₁ (95 / 100) z₁ u +
        sourcePrincipalPoissonResidueOuterSlice F hζ S₀ η v X Y Z σ₁ z₁ u := by
  rw [sourcePrincipalPoissonOuterSlice_eq_w_last F hζ S₀ η v X Y Z σ₁ σ₁ z₁ u hi,
    sourcePrincipalPoissonOuterSlice_eq_w_last F hζ S₀ η v X Y Z σ₁ (95 / 100) z₁ u hl,
    sourcePrincipalPoissonResidueOuterSlice_eq]
  let K := sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z
  let A (z : ℂ) := verticalIntegral σ₁ (fun w => K (V σ₁ u,w,z))
  let B (z : ℂ) := verticalIntegral (95 / 100) (fun w => K (V σ₁ u,w,z))
  let R := sourcePrincipalPoissonWResidue F hζ S₀ η v X Y Z (V σ₁ u)
  change verticalIntegral z₁ A = verticalIntegral z₁ B + verticalIntegral z₁ R
  have hB : Integrable (fun y : ℝ => B (V z₁ y)) := hl.integral_prod_right.const_mul N
  have hR : Integrable (fun y : ℝ => R (V z₁ y)) := hr
  rw [← verticalIntegral_add z₁ B R hB hR]
  unfold verticalIntegral
  apply congrArg (fun w : ℂ => N * w)
  apply integral_congr_ae
  filter_upwards with y
  exact sourcePrincipalPoissonW_shift F hζ S₀ η v hJ hcut hX hY hZ u y

include hJ hcut in
theorem sourcePrincipalPoissonIntegral_crossings {Z : ℝ} (hZ : 0 < Z) :
    sourcePrincipalPoissonIntegral F hζ S₀ η v
      (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z σ₁ σ₁ z₁ =
      sourcePrincipalPoissonDoubleConstant F hζ S₀ v *
        principalAngularGaussianSignal hζ η (sourceHilbertSet F S₀) Z +
        sourcePrincipalPoissonWRemainder F hζ S₀ η v Z +
        sourcePrincipalPoissonZRemainder F hζ S₀ η v Z := by
  let X := Z ^ (9 / 10 : ℝ)
  let Y := Z ^ (133 / 1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  have hσ : σ₁ ∈ Icc (95 / 100 : ℝ) 4 := by norm_num [sourcePrincipalSigma]
  have h95 : (95 / 100 : ℝ) ∈ Icc (95 / 100 : ℝ) 4 := by norm_num
  have h16 : (16 / 100 : ℝ) ∈ Icc (16 / 100 : ℝ) 2 := by norm_num
  let K := sourcePrincipalPoissonKernelOnLines F hζ S₀ η v X Y Z σ₁
  let R := sourcePrincipalPoissonWResidueOnLines F hζ S₀ η v X Y Z σ₁
  have hK {b c : ℝ} (hb : b ∈ Icc (95 / 100 : ℝ) 4) (hc : c ∈ Icc (16 / 100 : ℝ) 2)
      (hb' : b ≠ 1) (hc' : c ≠ 1 / 6) : Integrable (K b c) sourcePoissonHeightMeasure := by
    obtain ⟨_, _, h⟩ := sourcePrincipalPoissonIntegral_integrable_and_bound F hζ S₀ η v hJ hcut
      (a := σ₁) le_rfl hb hc hb' hc'
    exact (h hX hY hZ).1
  have hR {c : ℝ} (hc : c ∈ Icc (16 / 100 : ℝ) 2) (hc' : c ≠ 1 / 6) : Integrable (R c) μ₂ := by
    obtain ⟨_, _, h⟩ := sourcePrincipalPoissonResidueIntegral_integrable_and_bound F hζ S₀ η v hJ hcut
      (a := σ₁) le_rfl hc hc'
    exact (h hX hY hZ).1
  have hHi : Integrable (K σ₁ z₁) (Measure.prod μ₂ (volume : Measure ℝ)) :=
    hK hσ sourcePrincipalZetaLine_mem sourcePrincipalSigma_gt_one.ne' sourcePrincipalZetaLine_gt_sixth.ne'
  have hLo : Integrable (K (95 / 100) z₁) (Measure.prod μ₂ (volume : Measure ℝ)) :=
    hK h95 sourcePrincipalZetaLine_mem (by norm_num) sourcePrincipalZetaLine_gt_sixth.ne'
  have hRp : Integrable (R z₁) μ₂ := hR sourcePrincipalZetaLine_mem sourcePrincipalZetaLine_gt_sixth.ne'
  have hRm : Integrable (R (16 / 100)) μ₂ := hR h16 (by norm_num)
  let A := sourcePrincipalPoissonOuterSlice F hζ S₀ η v X Y Z σ₁ σ₁ z₁
  let B := sourcePrincipalPoissonOuterSlice F hζ S₀ η v X Y Z σ₁ (95 / 100) z₁
  let Rz := sourcePrincipalPoissonResidueOuterSlice F hζ S₀ η v X Y Z σ₁ (16 / 100)
  let C := sourcePrincipalPoissonDoubleConstant F hζ S₀ v
  let D := sourcePrincipalPoissonDoubleKernel F hζ S₀ η Z
  have hPoint : A =ᵐ[volume] fun u => (B u + Rz u) + C * D (V σ₁ u) := by
    filter_upwards [hHi.prod_left_ae, hLo.prod_left_ae, hRp.prod_left_ae] with u hi hl hr
    have hw := principalOuterSlice_w F hζ S₀ η v hJ hcut hX hY hZ u hi hl hr
    have hz := sourcePrincipalPoissonZ_shift F hζ S₀ η v hJ hcut hX hY hZ u
    dsimp only at hz
    rw [sourcePrincipalPoissonZRegularized_sixth F hζ S₀ η v hZ] at hz
    rw [sourcePrincipalPoissonResidueOuterSlice_eq] at hw
    rw [hz, ← sourcePrincipalPoissonResidueOuterSlice_eq] at hw
    change A u = B u + (Rz u + C * D (V σ₁ u)) at hw
    exact hw.trans (add_assoc _ _ _).symm
  have hB : Integrable B := sourcePrincipalPoissonOuterSlice_integrable F hζ S₀ η v X Y Z σ₁ (95 / 100) z₁ hLo
  have hRz : Integrable Rz := sourcePrincipalPoissonResidueOuterSlice_integrable F hζ S₀ η v X Y Z σ₁ (16 / 100) hRm
  obtain ⟨hDi, hD⟩ := sourcePrincipalPoissonDoubleKernel_outer_shift F hζ S₀ η hcut hZ
  change sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z σ₁ σ₁ z₁ =
    C * principalAngularGaussianSignal hζ η (sourceHilbertSet F S₀) Z +
      sourcePrincipalPoissonIntegral F hζ S₀ η v X Y Z σ₁ (95 / 100) z₁ +
      sourcePrincipalPoissonResidueIntegral F hζ S₀ η v X Y Z σ₁ (16 / 100)
  rw [sourcePrincipalPoissonIntegral_eq_outer F hζ S₀ η v X Y Z σ₁ σ₁ z₁ hHi]
  change N * (∫ u : ℝ, A u) = _
  have hSum : Integrable (fun u : ℝ => B u + Rz u) := hB.add hRz
  have hCLine : Integrable (fun u : ℝ => C * D (V σ₁ u)) := hDi.const_mul C
  rw [integral_congr_ae hPoint, integral_add hSum hCLine,
    integral_add hB hRz, integral_const_mul,
    sourcePrincipalPoissonIntegral_eq_outer F hζ S₀ η v X Y Z σ₁ (95 / 100) z₁ hLo,
    sourcePrincipalPoissonResidueIntegral_eq_outer F hζ S₀ η v X Y Z σ₁ (16 / 100) hRm,
    ← hD]
  change N * ((∫ u : ℝ, B u) + (∫ u : ℝ, Rz u) + C * (∫ u : ℝ, D (V σ₁ u))) =
    C * (N * ∫ u : ℝ, D (V σ₁ u)) + N * (∫ u : ℝ, B u) + N * (∫ u : ℝ, Rz u)
  ring

end
end ArtinMatthews.SourceEulerAssembly
