module

public import ArtinMatthews.SourceArchActualVector
public import ArtinMatthews.SourceArchWeightedProductMoment


set_option backward.privateInPublic true
@[expose] public section

/-! Positivity of the actual unit-frequency profile and of its compact
height tests at the exceptional parameter. -/
namespace ArtinMatthews.SourceArchJacquet
open ArtinMatthews.SourceReflection MeasureTheory
open scoped Topology MatrixGroups
noncomputable section

theorem sourceArchWeightedDiagonal_unit_whittaker {r : ℝ} (hr : 0 < r) :
    sourceArchWeightedDiagonalProfile sourceArchTraceCharacter (1/6) (-1) r =
      sourceArchSphericalWhittaker (Units.mk0 (r:ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')) := by
  let y : ℂˣ := Units.mk0 (r:ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
  have hn : ‖(y:ℂ)‖ = r := by
    change ‖(r:ℂ)‖ = r
    rw [Complex.norm_real,Real.norm_of_nonneg hr.le]
  have he := sourceArchWeightedDiagonalProfile_eq_integral sourceArchTraceCharacter (1/6) (-1) y
  rw [hn] at he
  rw [he]
  unfold sourceArchSphericalWhittaker
  apply integral_congr_ae
  filter_upwards with x
  rw [neg_one_mul,← sourceArchJacquetPhase_eq]
  exact mul_comm _ _

theorem sourceArchWeightedDiagonal_unit_positive {r : ℝ} (hr : 0 < r) :
    0 < (sourceArchWeightedDiagonalProfile sourceArchTraceCharacter (1/6) (-1) r).re ∧
      (sourceArchWeightedDiagonalProfile sourceArchTraceCharacter (1/6) (-1) r).im = 0 := by
  rw [sourceArchWeightedDiagonal_unit_whittaker hr]
  let y : ℂˣ := Units.mk0 (r:ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
  have hn : ‖(y:ℂ)‖ = r := by
    change ‖(r:ℂ)‖ = r
    rw [Complex.norm_real,Real.norm_of_nonneg hr.le]
  have hP := sourceArchSphericalWhittaker_sourceProfile y
  rw [hn,Real.sqrt_sq hr.le] at hP
  have hpos := sourceThetaBesselProfile_pos
    (show 0 < 4*Real.pi by positivity) (sq_pos_of_pos hr)
  have hreal : (sourceThetaBesselProfile (4*Real.pi) (r^2)).im = 0 := by
    rw [← Real.exp_log (sq_pos_of_pos hr),sourceThetaBesselProfile_exp_eq_moment
      (show 0 < 4*Real.pi by positivity),Complex.ofReal_im]
  have hre := congrArg Complex.re hP
  have him := congrArg Complex.im hP
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] at hre
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,add_zero,hreal] at him
  constructor
  · have hc := sourceArchJacquetConstant_pos
    have hmul : 0 < sourceArchJacquetConstant*(sourceThetaBesselProfile (4*Real.pi) (r^2)).re :=
      mul_pos hc hpos
    rw [hre] at hmul
    exact (mul_pos_iff_of_pos_left hr).mp hmul
  · exact (mul_eq_zero.mp him.symm).resolve_left hr.ne'

theorem sourceArchUnitFrequencyProduct_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (hy : ∀ i, 0 < y i) :
    0 < (sourceArchWeightedProduct (fun _ : ι => sourceArchTraceCharacter)
      (fun _ => -1) (1/6) y).re ∧
      (sourceArchWeightedProduct (fun _ : ι => sourceArchTraceCharacter)
        (fun _ => -1) (1/6) y).im = 0 := by
  let F := fun i : ι => sourceArchWeightedDiagonalProfile sourceArchTraceCharacter (1/6) (-1) (y i)
  have hF (i : ι) : F i = ((F i).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      exact (sourceArchWeightedDiagonal_unit_positive (hy i)).2
  have he : sourceArchWeightedProduct (fun _ : ι => sourceArchTraceCharacter)
      (fun _ => -1) (1/6) y = ((∏ i, (F i).re : ℝ):ℂ) := by
    unfold sourceArchWeightedProduct
    calc
      _ = ∏ i, ((F i).re:ℂ) := Finset.prod_congr rfl (fun i _ => hF i)
      _ = _ := (map_prod Complex.ofRealHom (fun i => (F i).re) Finset.univ).symm
  rw [he,Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨Finset.prod_pos (fun i _ => (sourceArchWeightedDiagonal_unit_positive (hy i)).1),rfl⟩

end
end ArtinMatthews.SourceArchJacquet
