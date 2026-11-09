module

public import ArtinMatthews.SourceKPCompactWeakCutoffBound
public import ArtinMatthews.SourceKPCompactHeightTail
public import ArtinMatthews.SourceKPCompactExhaustionEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact exhaustion approximants are Cauchy in the form norm. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff InnerProductSpace Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "HY" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "Ω" => productUpper (InfinitePlace K)
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "V" => SourceKPCompactH1 K hζ

def sourceKPCompactWeakExhaustionCore (w : Y → ℂ) (hw : Continuous w)
    (hwd : ∀ b, ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ w b) Ω) (n : ℕ) : T :=
  sourceKPCompactCoreMul K hζ (sourceKPCompactExhaustionC2 K hζ n) w hw hwd

theorem sourceKPCompactWeakExhaustionCore_locally_eq (w : Y → ℂ) (hw : Continuous w)
    (hwd : ∀ b, ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ w b) Ω)
    (S : Set Y) (hS : IsCompact S) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ S,
      (sourceKPCompactWeakExhaustionCore K hζ w hw hwd n).val =ᶠ[𝓝 y] w := by
  obtain ⟨N,hN⟩ := sourceKPAutomorphicExhaustionCutoff_compact_eventually_locally_one K hζ S hS
  refine ⟨N,?_⟩
  intro n hn y hy
  filter_upwards [hN n hn y hy] with x hx
  change ((sourceKPAutomorphicExhaustionCutoff K hζ n x : ℝ) : ℂ) * w x = w x
  rw [show sourceKPAutomorphicExhaustionCutoff K hζ n x = 1 from hx,Complex.ofReal_one,one_mul]

theorem sourceKPCompactWeakExhaustion_cauchy (w d : Y → ℂ) (lam : ℂ) (hw : Continuous w)
    (hwd : ∀ b, ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ w b) Ω)
    (hwL : MemLp w 2 μY) (R₀ : ℝ) (hd : ∀ y, R₀ < HY y → d y = 0)
    (hweak : ∀ φ : T, ∃ S : Set Y, IsCompact S ∧ ∀ v : T,
      (∀ y ∈ S, v.val =ᶠ[𝓝 y] w) →
        sourceKPCompactDirichletCore K hζ φ v = ∫ y, star (φ.val y)*(lam*w y-d y) ∂μY) :
    CauchySeq (fun n => sourceKPCompactH1Core K hζ
      ⟨sourceKPCompactWeakExhaustionCore K hζ w hw hwd n⟩) := by
  let η := sourceKPCompactExhaustionC2 K hζ
  let u : ℕ → V := fun n => sourceKPCompactH1Core K hζ
    ⟨sourceKPCompactWeakExhaustionCore K hζ w hw hwd n⟩
  change CauchySeq u
  obtain ⟨C,hC,hCbound⟩ := sourceKPCompactExhaustion_energy_uniform K hζ
  let L := 2^2*(1+‖lam‖)+4*C
  have hL : 0 < L := by dsimp only [L]; positivity
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let tail := fun R : ℕ => ∫ y in {y | (R : ℝ) < HY y}, ‖w y‖^2 ∂μY
  have ht : Tendsto tail atTop (𝓝 0) := sourceKPCompactHeightTail_tendsto K hζ w hwL
  obtain ⟨Rmin,hRmin⟩ := exists_nat_ge R₀
  obtain ⟨R,hRsmall,hRge⟩ := ((ht.eventually (gt_mem_nhds (div_pos (sq_pos_of_pos hε) hL))).and
    (eventually_ge_atTop Rmin)).exists
  let S : Set Y := {y | HY y ≤ (R : ℝ)}
  have hS : IsCompact S := sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ R
  have hSd (y : Y) (hy : y ∉ S) : d y = 0 :=
    hd y ((hRmin.trans (Nat.cast_le.mpr hRge)).trans_lt (lt_of_not_ge hy))
  obtain ⟨N,hN⟩ := sourceKPAutomorphicExhaustionCutoff_compact_eventually_locally_one K hζ S hS
  refine ⟨N,?_⟩
  intro m hm n hn
  let a := η m-η n
  have ha0 (y : Y) (hy : y ∈ S) : a.val =ᶠ[𝓝 y] 0 := by
    filter_upwards [hN m hm y hy,hN n hn y hy] with x hx hy'
    change (η m).val x-(η n).val x = 0
    rw [sourceKPCompactExhaustionC2_apply,sourceKPCompactExhaustionC2_apply,hx,hy',sub_self]
  have haR (y : Y) : (a.val y).im = 0 := by
    change ((η m).val y-(η n).val y).im = 0
    rw [sourceKPCompactExhaustionC2_apply,sourceKPCompactExhaustionC2_apply,
      Complex.sub_im,Complex.ofReal_im,Complex.ofReal_im,sub_zero]
  have haN (y : Y) : ‖a.val y‖ ≤ 2 := by
    change ‖(η m).val y-(η n).val y‖ ≤ 2
    calc
      _ ≤ ‖(η m).val y‖+‖(η n).val y‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [sourceKPCompactExhaustionC2_norm_le_one K hζ m y,
        sourceKPCompactExhaustionC2_norm_le_one K hζ n y]
  have haE (y : Y) : sourceKPCompactCoreEnergy K hζ a y ≤ 4*C := by
    exact (sourceKPCompactCoreEnergy_sub_le K hζ (η m) (η n) y).trans
      (by linarith [hCbound m y,hCbound n y])
  have hb := sourceKPCompactWeakCutoff_bound K hζ w d lam hw hwd hwL hweak a haR
    (M := 2) (B := 4*C) (by norm_num) (by positivity) haN haE S hS.measurableSet hSd ha0
  have hcomp : Sᶜ = {y | (R : ℝ) < HY y} := by ext y; simp [S,not_le]
  rw [hcomp] at hb
  have hdif : u m-u n = sourceKPCompactH1Core K hζ ⟨sourceKPCompactCoreMul K hζ a w hw hwd⟩ := by
    dsimp only [u]
    rw [← map_sub]
    congr 1
    apply (sourceKPCompactFormCoreLinearEquiv K hζ).injective
    apply Subtype.ext
    funext y
    change (η m).val y*w y-(η n).val y*w y = ((η m).val y-(η n).val y)*w y
    ring
  have hsq : ‖u m-u n‖^2 < ε^2 := by
    rw [hdif]
    have hlt := (lt_div_iff₀ hL).mp hRsmall
    exact hb.trans_lt (by simpa only [L,tail,mul_comm] using hlt)
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (u m-u n)]

end
end ArtinMatthews
