module

public import ArtinMatthews.SourceKPCompactTestBumps
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition


set_option backward.privateInPublic true
@[expose] public section

/-! Finite decompositions of actual compact tests by local periodizations. -/

namespace ArtinMatthews
open NumberField Filter Topology SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "P" => ProductSpace (InfinitePlace K)
local notation "Ω" => productUpper (InfinitePlace K)
local notation "T" => sourceKPCompactC2Core K hζ

theorem sourceKPCompactCore_sum_periodized_tests (φ : T) :
    ∃ (I : Finset Y) (b : Y → SourceKPFiniteLevelFiber K hζ)
      (p : Y → SourceKPArchUpperHalfSpace K)
      (η : ∀ i, h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ (b i) (p i))),
      φ.val = fun y => ∑ i ∈ I, sourceKPChartPeriodizationGlobal K hζ (b i) (η i).val y := by
  have hcover (y : Y) : ∃ (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K),
      ∃ η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p),
        (∀ x, 0 ≤ (η.val.val x).re ∧ (η.val.val x).im = 0) ∧
        1 ≤ (sourceKPChartPeriodizationGlobal K hζ b η.val y).re := by
    obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    obtain ⟨η,hη,hp⟩ := sourceKPCompactPositiveLocalTest K hζ b p
    exact ⟨b,p,η,hη,hp⟩
  choose b p η hη hcenter using hcover
  let B (i : Y) : T := sourceKPChartPeriodizationCore K hζ (b i) (η i).val
  have hreal (i y : Y) : 0 ≤ ((B i).val y).re ∧ ((B i).val y).im = 0 :=
    sourceKPChartPeriodizationGlobal_real_nonneg K hζ (b i) (η i).val (hη i) y
  let U (i : Y) : Set Y := {y | (1/2 : ℝ) < ((B i).val y).re}
  have hU (i : Y) : IsOpen (U i) :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (B i).prop.1)
  have hself (i : Y) : i ∈ U i := by
    change (1/2 : ℝ) < ((B i).val i).re
    exact lt_of_lt_of_le (by norm_num) (hcenter i)
  obtain ⟨I,hI⟩ := φ.prop.2.1.elim_finite_subcover U hU
    (fun y _ => Set.mem_iUnion.mpr ⟨y,hself y⟩)
  let S : Y → ℝ := fun y => ∑ i ∈ I, ((B i).val y).re
  have hS (y : Y) : 0 ≤ S y := Finset.sum_nonneg (fun i _ => (hreal i y).1)
  have hSlarge {y : Y} (hy : y ∈ tsupport φ.val) : (1/2 : ℝ) < S y := by
    obtain ⟨i,hi,hyU⟩ := Set.mem_iUnion₂.mp (hI hy)
    exact (show (1/2 : ℝ) < ((B i).val y).re from hyU).trans_le
      (Finset.single_le_sum (fun j _ => (hreal j y).1) hi)
  have hScont : Continuous S := continuous_finsetSum _ (fun i _ =>
    Complex.continuous_re.comp (B i).prop.1)
  let d (y : Y) : ℝ := S y + Real.smoothTransition (1-2*S y)
  have hdpos (y : Y) : 0 < d y := by
    by_cases hy : S y = 0
    · simp [d,hy]
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hS y) (Ne.symm hy)) (Real.smoothTransition.nonneg _)
  have hdS {y : Y} (hy : y ∈ tsupport φ.val) : d y = S y := by
    have hs := hSlarge hy
    rw [show d y = S y + Real.smoothTransition (1-2*S y) from rfl,
      Real.smoothTransition.zero_of_nonpos (by linarith),add_zero]
  let R : Y → ℂ := fun y => (d y : ℂ)⁻¹
  have hRcont : Continuous R := by
    apply (Complex.continuous_ofReal.comp (hScont.add
      (Real.smoothTransition.continuous.comp (continuous_const.sub (continuous_const.mul hScont))))).inv₀
    intro y
    exact Complex.ofReal_ne_zero.mpr (hdpos y).ne'
  have hRdiff (c : SourceKPFiniteLevelFiber K hζ) :
      ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ R c) Ω := by
    let e : P → Y := fun x => sourceKPUpperToCompact K hζ c (sourceKPArchEuclideanUpperMap K x)
    have hs : ContDiffOn ℝ 2 (fun x => S (e x)) Ω := by
      apply ContDiffOn.sum
      intro i _
      have hb := Complex.reCLM.contDiff.comp_contDiffOn ((B i).prop.2.2 c)
      apply hb.congr
      intro x hx
      simp only [Function.comp_def,sourceKPCompactChartPullback,ite_eq_left hx,e,Complex.reCLM_apply]
    have hd : ContDiffOn ℝ 2 (fun x => d (e x)) Ω :=
      hs.add (Real.smoothTransition.contDiff.comp_contDiffOn
        (contDiffOn_const.sub (contDiffOn_const.mul hs)))
    apply ((Complex.ofRealCLM.contDiff.comp_contDiffOn hd).inv
      (fun x _ => Complex.ofReal_ne_zero.mpr (hdpos (e x)).ne')).congr
    intro x hx
    simp only [Function.comp_def,sourceKPCompactChartPullback,ite_eq_left hx,e,R,
      Complex.ofRealCLM_apply] <;> rfl
  let F := sourceKPCompactCoreMul K hζ φ R hRcont hRdiff
  refine ⟨I,b,p,fun i => sourceKPCompactCoreLocalized K hζ F (b i) (p i) (η i),?_⟩
  funext y
  simp_rw [sourceKPChartPeriodizationGlobal_localized,Pi.mul_apply]
  change φ.val y = ∑ i ∈ I, (B i).val y * F.val y
  rw [← Finset.sum_mul]
  have hsum : (∑ i ∈ I, (B i).val y) = (S y : ℂ) := by
    apply Complex.ext
    · rw [Complex.re_sum,Complex.ofReal_re]
    · rw [Complex.im_sum,Complex.ofReal_im]
      exact Finset.sum_eq_zero (fun i _ => (hreal i y).2)
  rw [hsum]
  change φ.val y = (S y : ℂ) * (φ.val y * R y)
  by_cases hy : y ∈ tsupport φ.val
  · have hn : (S y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hSlarge hy])
    rw [show R y = (d y : ℂ)⁻¹ from rfl,hdS hy,mul_comm (φ.val y),← mul_assoc,
      mul_inv_cancel₀ hn,one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy,zero_mul,mul_zero]

end
end ArtinMatthews
