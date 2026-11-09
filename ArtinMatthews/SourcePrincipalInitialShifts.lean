module

public import ArtinMatthews.SourcePrincipalContourBounds
public import ArtinMatthews.SourcePrincipalContourGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! All three initial principal contour moves are pole-free. -/

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain Set MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
variable (hJ : J ≠ ⊥) (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
variable {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
local notation "σ₁" => sourcePrincipalSigma
local notation "z₁" => sourcePrincipalZetaLine
local notation "H" => sourceContourHeightWeight
local notation "V" => sourcePoissonVertical
local notation "K" => sourcePrincipalPoissonKernel F hζ S₀ η v X Y Z

include hJ hcut hX hY hZ in
private theorem principalKernel_right_path {D : Set ℂ}
    (p : ℂ → ProbeCoordinates) (hp : DifferentiableOn ℂ p D)
    (h : ∀ s ∈ D, σ₁ ≤ (p s).1.re ∧ σ₁ ≤ (p s).2.1.re ∧ z₁ ≤ (p s).2.2.re) :
    DifferentiableOn ℂ (fun s => K (p s)) D := by
  apply sourcePrincipalPoissonKernel_differentiableOn_path F hζ S₀ η v hJ hcut hX hY hZ p hp
  · intro s hs
    obtain ⟨hξ, hw, hz⟩ := h s hs
    exact ⟨sourcePrincipalSigma_gt_one.trans_le hξ,
      (by norm_num [sourcePrincipalSigma] : (94999 / 100000 : ℝ) < σ₁).trans_le hw,
      (by norm_num [sourcePrincipalZetaLine] : (15999 / 100000 : ℝ) < z₁).trans_le hz⟩
  · intro s hs he
    have hh := sourcePrincipalSigma_gt_one.trans_le (h s hs).2.1
    rw [he, Complex.one_re] at hh
    exact lt_irrefl _ hh
  · intro s hs he
    have hh := sourcePrincipalZetaLine_gt_sixth.trans_le (h s hs).2.2
    rw [he, show ((1 / 6 : ℂ)).re = 1 / 6 by norm_num [Complex.div_re]] at hh
    exact lt_irrefl _ hh

include hcut hX hY hZ in
private theorem principalKernel_initial_height_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc σ₁ 4, ∀ b ∈ Icc σ₁ 4, ∀ c ∈ Icc z₁ 2,
      ∀ u t y : ℝ, ‖K (V a u, V b t, V c y)‖ ≤
        C * ((H t * H y) * Real.exp (-((u + y) ^ 2))) := by
  let δ : ℝ := 1 / 10000000
  have hδ : 0 < δ := by norm_num [δ]
  obtain ⟨C, hC, hb⟩ := sourcePrincipalPoissonKernel_height_bound F hζ S₀ η v hcut δ δ hδ hδ
  obtain ⟨B, hB, hscale⟩ := sourcePrincipalTripleScale_bounded hX hY hZ
  refine ⟨C * B, mul_nonneg hC hB, fun a ha b hb' c hc u t y => ?_⟩
  have hw : δ ≤ ‖V b t - 1‖ := calc
    δ ≤ b - 1 := by
      have hh := hb'.1
      unfold sourcePrincipalSigma at hh
      dsimp [δ]
      linarith
    _ ≤ |b - 1| := le_abs_self _
    _ ≤ _ := sourcePrincipalVertical_w_gap_re b t
  have hz : δ ≤ ‖(6 : ℂ) * V c y - 1‖ := calc
    δ ≤ 6 * c - 1 := by
      have hh := hc.1
      unfold sourcePrincipalZetaLine at hh
      dsimp [δ]
      linarith
    _ ≤ |6 * c - 1| := le_abs_self _
    _ ≤ _ := sourcePrincipalVertical_z_gap_re c y
  have hw' : b ∈ Icc (95 / 100 : ℝ) 4 :=
    ⟨(by norm_num [sourcePrincipalSigma] : (95 / 100 : ℝ) ≤ σ₁).trans hb'.1, hb'.2⟩
  have hz' : c ∈ Icc (16 / 100 : ℝ) 2 := ⟨sourcePrincipalZetaLine_mem.1.trans hc.1, hc.2⟩
  exact (hb hX hY hZ a ha.1 b hw' c hz' u t y hw hz).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hscale a ha b hw' c hz') hC)
      (mul_nonneg (mul_nonneg (sourceContourHeightWeight_nonneg _) (sourceContourHeightWeight_nonneg _))
        (Real.exp_nonneg _)))

include hJ hcut hX hY hZ in
theorem sourcePrincipalPoissonInitialShifts_pointwise (u t y : ℝ) :
    ((∫ r : ℝ, K (V 4 u, V 4 t, V 2 r)) = ∫ r : ℝ, K (V 4 u, V 4 t, V z₁ r)) ∧
    ((∫ r : ℝ, K (V 4 u, V 4 r, V z₁ y)) = ∫ r : ℝ, K (V 4 u, V σ₁ r, V z₁ y)) ∧
    ((∫ r : ℝ, K (V 4 r, V σ₁ t, V z₁ y)) = ∫ r : ℝ, K (V σ₁ r, V σ₁ t, V z₁ y)) := by
  obtain ⟨C, hC, hb⟩ := principalKernel_initial_height_bound F hζ S₀ η v hcut hX hY hZ
  have ha : 4 ∈ Icc σ₁ (4 : ℝ) := ⟨sourcePrincipalSigma_le_four, le_rfl⟩
  have hσ : σ₁ ∈ Icc σ₁ (4 : ℝ) := ⟨le_rfl, sourcePrincipalSigma_le_four⟩
  have hz : z₁ ∈ Icc z₁ (2 : ℝ) := ⟨le_rfl, sourcePrincipalZetaLine_mem.2⟩
  have hg (a b : ℝ) : Real.exp (-((a+b)^2)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · let L (s : ℂ) := K (V 4 u, V 4 t, s)
    have hL : DifferentiableOn ℂ L {s : ℂ | z₁ ≤ s.re ∧ s.re ≤ 2} :=
      principalKernel_right_path F hζ S₀ η v hJ hcut hX hY hZ (fun s => (V 4 u, V 4 t, s))
        ((differentiableOn_const _).prodMk ((differentiableOn_const _).prodMk differentiableOn_id))
        (fun _ hs => ⟨by simpa using ha.1, by simpa using ha.1, hs.1⟩)
    have hB (c : ℝ) (hc : c ∈ Icc z₁ 2) (r : ℝ) : ‖L (V c r)‖ ≤ C * H r := by
      apply (hb 4 ha 4 ha c hc u t r).trans
      apply mul_le_mul_of_nonneg_left _ hC
      exact (mul_le_of_le_one_right
        (mul_nonneg (sourceContourHeightWeight_nonneg t) (sourceContourHeightWeight_nonneg r)) (hg u r)).trans
        (mul_le_of_le_one_left (sourceContourHeightWeight_nonneg r) (sourceContourHeightWeight_le_one t))
    exact (source_vertical_integral_eq_of_heightWeight L hz.2 hL hB).symm
  · let L (s : ℂ) := K (V 4 u, s, V z₁ y)
    have hL : DifferentiableOn ℂ L {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ 4} :=
      principalKernel_right_path F hζ S₀ η v hJ hcut hX hY hZ (fun s => (V 4 u, s, V z₁ y))
        ((differentiableOn_const _).prodMk (differentiableOn_id.prodMk (differentiableOn_const _)))
        (fun _ hs => ⟨by simpa using ha.1, hs.1, by simp⟩)
    have hB (b : ℝ) (hb' : b ∈ Icc σ₁ 4) (r : ℝ) : ‖L (V b r)‖ ≤ C * H r := by
      apply (hb 4 ha b hb' z₁ hz u r y).trans
      apply mul_le_mul_of_nonneg_left _ hC
      exact (mul_le_of_le_one_right
        (mul_nonneg (sourceContourHeightWeight_nonneg r) (sourceContourHeightWeight_nonneg y)) (hg u y)).trans
        (mul_le_of_le_one_right (sourceContourHeightWeight_nonneg r) (sourceContourHeightWeight_le_one y))
    exact (source_vertical_integral_eq_of_heightWeight L hσ.2 hL hB).symm
  · let L (s : ℂ) := K (s, V σ₁ t, V z₁ y)
    have hL : DifferentiableOn ℂ L {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ 4} :=
      principalKernel_right_path F hζ S₀ η v hJ hcut hX hY hZ (fun s => (s, V σ₁ t, V z₁ y))
        (differentiableOn_id.prodMk ((differentiableOn_const _).prodMk (differentiableOn_const _)))
        (fun _ hs => ⟨hs.1, by simp, by simp⟩)
    have hB (a : ℝ) (ha' : a ∈ Icc σ₁ 4) (r : ℝ) :
        ‖L (V a r)‖ ≤ (C * (2 * (1 + y^2))) * H r := by
      have hH : H t * H y ≤ 1 :=
        (mul_le_of_le_one_left (sourceContourHeightWeight_nonneg y) (sourceContourHeightWeight_le_one t)).trans
          (sourceContourHeightWeight_le_one y)
      calc
        _ ≤ C * ((H t * H y) * Real.exp (-((r + y) ^ 2))) := hb a ha' σ₁ hσ z₁ hz r t y
        _ ≤ C * Real.exp (-((r + y) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (Real.exp_nonneg _) hH) hC
        _ ≤ C * (2 * (1 + y^2) * H r) :=
          mul_le_mul_of_nonneg_left (sourceGaussian_translate_le_heightWeight r y) hC
        _ = _ := by ring
    exact (source_vertical_integral_eq_of_heightWeight L hσ.2 hL hB).symm

end
end ArtinMatthews.SourceEulerAssembly
