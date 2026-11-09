module

public import ArtinMatthews.SourceKPCompactWeakExhaustionCauchy
public import ArtinMatthews.SourceKPCompactH1WeakTests
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of the form limit with the literal weak solution. -/
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

theorem sourceKPCompactWeakExhaustion_realization (w d : Y → ℂ) (lam : ℂ) (hw : Continuous w)
    (hwd : ∀ b, ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ w b) Ω)
    (hwL : MemLp w 2 μY) (R₀ : ℝ) (hd : ∀ y, R₀ < HY y → d y = 0)
    (hweak : ∀ φ : T, ∃ S : Set Y, IsCompact S ∧ ∀ v : T,
      (∀ y ∈ S, v.val =ᶠ[𝓝 y] w) →
        sourceKPCompactDirichletCore K hζ φ v = ∫ y, star (φ.val y)*(lam*w y-d y) ∂μY) :
    ∃ u : V, (sourceKPCompactH1Mass K hζ u : Y → ℂ) =ᵐ[μY] w ∧
      ∀ φ : T, sourceKPCompactH1Dirichlet K hζ (sourceKPCompactH1Core K hζ ⟨φ⟩) u =
        ∫ y, star (φ.val y)*(lam*w y-d y) ∂μY := by
  let Q := sourceKPCompactWeakExhaustionCore K hζ w hw hwd
  let v : ℕ → V := fun n => sourceKPCompactH1Core K hζ ⟨Q n⟩
  let j := sourceKPCompactH1Mass K hζ
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete
    (sourceKPCompactWeakExhaustion_cauchy K hζ w d lam hw hwd hwL R₀ hd hweak)
  have hj : Tendsto (fun n => j (v n)) atTop (𝓝 (j u)) := (j.continuous.tendsto u).comp hu
  obtain ⟨k,hk,hkae⟩ := (tendstoInMeasure_of_tendsto_Lp hj).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ y ∂μY, ∀ n, (j (v n) : Y → ℂ) y = (Q n).val y := by
    apply ae_all_iff.mpr
    intro n
    dsimp only [j,v]
    rw [sourceKPCompactH1Mass_core]
    exact sourceKPCompactCoreMass_coe K hζ (Q n)
  refine ⟨u,?_,?_⟩
  · filter_upwards [hkae,hcoe] with y hy hcy
    obtain ⟨N,hN⟩ := sourceKPAutomorphicExhaustionCutoff_eventually_locally_one K hζ y
    have he : (fun n => (j (v (k n)) : Y → ℂ) y) =ᶠ[atTop] fun _ => w y := by
      filter_upwards [hk.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
      rw [hcy (k n)]
      change ((sourceKPAutomorphicExhaustionCutoff K hζ (k n) y : ℝ) : ℂ)*w y = w y
      have h : sourceKPAutomorphicExhaustionCutoff K hζ (k n) y = 1 :=
        (hN (k n) hn).eq_of_nhds
      rw [h,Complex.ofReal_one,one_mul]
    exact tendsto_nhds_unique hy (tendsto_const_nhds.congr' he.symm)
  · intro φ
    obtain ⟨S,hS,h⟩ := hweak φ
    obtain ⟨N,hN⟩ := sourceKPCompactWeakExhaustionCore_locally_eq K hζ w hw hwd S hS
    let a := sourceKPCompactH1Dirichlet K hζ (sourceKPCompactH1Core K hζ ⟨φ⟩)
    have ha : Tendsto (fun n => a (v n)) atTop (𝓝 (a u)) :=
      ((sourceKPCompactH1Dirichlet_continuous_right K hζ
        (sourceKPCompactH1Core K hζ ⟨φ⟩)).tendsto u).comp hu
    have he : (fun n => a (v n)) =ᶠ[atTop] fun _ =>
        ∫ y, star (φ.val y)*(lam*w y-d y) ∂μY := by
      filter_upwards [eventually_ge_atTop N] with n hn
      dsimp only [a,v]
      rw [sourceKPCompactH1Dirichlet_core]
      exact h (Q n) (hN n hn)
    exact tendsto_nhds_unique ha (tendsto_const_nhds.congr' he.symm)

end
end ArtinMatthews
