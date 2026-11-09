module

public import ArtinMatthews.SpectralContinuousCyclicMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Dominated convergence in the actual complex L² norm, using the
literal representatives of the completed vectors. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ArtinMatthews

theorem spectralLp2_tendsto_of_domination {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ℕ → Lp ℂ 2 μ) (g : Lp ℂ 2 μ) (F : ℕ → X → ℂ) (G : X → ℂ)
    (hF : ∀ n, ⇑(f n)=ᵐ[μ] F n) (hG : ⇑g=ᵐ[μ] G)
    (hlim : ∀ᵐ x ∂μ,Tendsto (fun n => F n x) atTop (𝓝 (G x)))
    (B : X → ℝ) (hB : Integrable B μ) (hDom : ∀ n,∀ᵐ x ∂μ,‖F n x-G x‖^2≤B x) :
    Tendsto f atTop (𝓝 g) := by
  let I (n : ℕ) (x : X) := ‖F n x-G x‖^2
  have hi : Tendsto (fun n => ∫ x,I n x ∂μ) atTop (𝓝 (∫ _ : X, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · exact Eventually.of_forall fun n =>
        (((Lp.aestronglyMeasurable (f n)).congr (hF n)).sub ((Lp.aestronglyMeasurable g).congr hG)).norm.pow 2
    · exact Eventually.of_forall fun n => (hDom n).mono fun x hx => by
        change ‖‖F n x-G x‖^2‖≤B x
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hx
    · exact hB
    · filter_upwards [hlim] with x hx
      have ht := ((hx.sub (tendsto_const_nhds (x:=G x))).norm).pow 2
      simpa only [I,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht
  simp only [integral_zero] at hi
  have hEq (n : ℕ) : (∫ x,I n x ∂μ)=‖f n-g‖^2 := by
    rw [spectralLp2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f n) g,hF n,hG] with x hx hfx hgx
    change ‖F n x-G x‖^2=‖(f n-g) x‖^2
    rw [hx,Pi.sub_apply,hfx,hgx]
  have hn := hi.congr hEq
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs)

end ArtinMatthews
