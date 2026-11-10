module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Topology.Algebra.Module.ModuleTopology


set_option backward.privateInPublic true
@[expose] public section

/-! Local C² termwise summation from genuine first and second derivative majorants. -/
noncomputable section
open Set Filter
open scoped ContDiff
namespace ArtinMatthews

theorem spectralLocalC2Series {ι : Type*} (f : ι → (ℝ × ℝ) → ℂ)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) U)
    (u₁ u₂ : ι → ℝ) (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    (h₁ : ∀ i p, p ∈ U → ‖fderiv ℝ (f i) p‖ ≤ u₁ i)
    (h₂ : ∀ i p, p ∈ U → ‖fderiv ℝ (fderiv ℝ (f i)) p‖ ≤ u₂ i)
    (p₀ : ℝ × ℝ) (hp₀ : p₀ ∈ U) (hsum : Summable (fun i => f i p₀)) :
    ContDiffOn ℝ 2 (fun p => ∑' i, f i p) U ∧
    ∀ p ∈ U,
      fderiv ℝ (fun q => ∑' i, f i q) p = ∑' i, fderiv ℝ (f i) p ∧
      fderiv ℝ (fderiv ℝ (fun q => ∑' i, f i q)) p = ∑' i, fderiv ℝ (fderiv ℝ (f i)) p := by
  let g₁ := fun p => ∑' i, fderiv ℝ (f i) p
  let g₂ := fun p => ∑' i, fderiv ℝ (fderiv ℝ (f i)) p
  have hd₁ (i : ι) (p : ℝ × ℝ) (hp : p ∈ U) :
      HasFDerivAt (f i) (fderiv ℝ (f i) p) p :=
    ((hf i).differentiableOn (by norm_num) p hp).differentiableAt (hU.mem_nhds hp) |>.hasFDerivAt
  have hd₂ (i : ι) (p : ℝ × ℝ) (hp : p ∈ U) :
      HasFDerivAt (fderiv ℝ (f i)) (fderiv ℝ (fderiv ℝ (f i)) p) p :=
    (((hf i).fderiv_of_isOpen hU (by norm_num : (1:ℕ∞ω)+1≤2)).differentiableOn
      (by norm_num) p hp).differentiableAt (hU.mem_nhds hp) |>.hasFDerivAt
  have hsum₁ : Summable (fun i => fderiv ℝ (f i) p₀) :=
    hu₁.of_norm_bounded (fun i => h₁ i p₀ hp₀)
  have hD₁ (p : ℝ × ℝ) (hp : p ∈ U) :
      HasFDerivAt (fun q => ∑' i, f i q) (g₁ p) p :=
    hasFDerivAt_tsum_of_isPreconnected hu₁ hU hUc hd₁ h₁ hp₀ hsum hp
  have hD₂ (p : ℝ × ℝ) (hp : p ∈ U) : HasFDerivAt g₁ (g₂ p) p :=
    hasFDerivAt_tsum_of_isPreconnected hu₂ hU hUc hd₂ h₂ hp₀ hsum₁ hp
  have hc₂ : ContinuousOn g₂ U := by
    dsimp only [g₂]
    apply (tendstoUniformlyOn_tsum
      (f := fun i p => fderiv ℝ (fderiv ℝ (f i)) p) (s := U) hu₂ h₂).continuousOn
    apply (Eventually.of_forall (fun s : Finset ι =>
      continuousOn_finsetSum s (fun i _ =>
        (((hf i).fderiv_of_isOpen hU (by norm_num : (1:ℕ∞ω)+1≤2)).fderiv_of_isOpen hU
          (by norm_num : (0:ℕ∞ω)+1≤1)).continuousOn))).frequently
  have hc₁ : ContDiffOn ℝ 1 g₁ U := by
    rw [show (1:ℕ∞ω) = 0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (hD₂ p hp).differentiableAt.differentiableWithinAt,?_,?_⟩
    · norm_num
    · rw [contDiffOn_zero]
      exact hc₂.congr (fun p hp => (hD₂ p hp).fderiv)
  have hc : ContDiffOn ℝ 2 (fun p => ∑' i, f i p) U := by
    rw [show (2:ℕ∞ω) = 1+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (hD₁ p hp).differentiableAt.differentiableWithinAt,?_,?_⟩
    · norm_num
    · exact hc₁.congr (fun p hp => (hD₁ p hp).fderiv)
  refine ⟨hc,?_⟩
  intro p hp
  refine ⟨(hD₁ p hp).fderiv,?_⟩
  have he : (fderiv ℝ (fun q => ∑' i, f i q)) =ᶠ[nhds p] g₁ := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (hD₁ q hq).fderiv
  exact he.fderiv_eq.trans (hD₂ p hp).fderiv

end ArtinMatthews
