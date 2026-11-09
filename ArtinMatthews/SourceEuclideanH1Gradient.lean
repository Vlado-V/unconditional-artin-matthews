module

public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient
public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDerivativeCoordinates
public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv


set_option backward.privateInPublic true
@[expose] public section

/-! The Euclidean (H^1) coordinate of a genuine mass and weak-gradient
pair, with the exact Fourier normalization of the vector gradient. -/

namespace ArtinMatthews

open MeasureTheory TemperedDistribution Filter
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped SchwartzMap LineDeriv Topology

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

local notation "J" => SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
local notation "grad" => EuclideanGradient.CM.Construction.sobolevVectorGradient
local notation "component" => LpComponents.CM.Construction.complexLpComponent (volume : Measure E)
local notation "cF" => (2 * Real.pi * Complex.I : ℂ)

theorem sourceEuclideanH1_of_weak_gradient (b : OrthonormalBasis ι ℝ E)
    (M : Lp ℂ 2 (volume : Measure E)) (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hG : ∀ i, ∂_{b i} (M : 𝓢'(E, ℂ)) = (component i G : 𝓢'(E, ℂ))) :
    ∃ u : Lp ℂ 2 (volume : Measure E), J u = M ∧ cF • grad b u = G := by
  have hM : MemSobolev 1 2 (M : 𝓢'(E, ℂ)) := by
    rw [← zero_add (1 : ℝ)]
    apply (SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b 0 _).mpr
    refine ⟨memSobolev_zero_iff.mpr ⟨M,rfl⟩,fun i => ?_⟩
    rw [hG i]
    exact memSobolev_zero_iff.mpr ⟨component i G,rfl⟩
  obtain ⟨u,hu⟩ := (SobolevDerivativeCoordinates.CM.Construction.memSobolev_l2_iff_embedding_range
    (by norm_num : (0 : ℝ) ≤ 1) M).mp hM
  let d := FourierEnergy.CM.Construction.sobolevNormalizedGradient b u
  have hd (i : ι) : cF • d i = component i G := by
    change cF • FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i = component i G
    rw [← FourierEnergy.CM.Construction.sobolevNormalizedGradient_derivative]
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
    change (SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) u : 𝓢'(E, ℂ)) =
      (component i G : 𝓢'(E, ℂ))
    rw [SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution,hu,hG i]
  have hcomp : ∀ᵐ x ∂(volume : Measure E), ∀ i, cF • d i x = G x i := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul cF (d i), LpComponents.CM.Construction.complexLpComponent_coe
      (volume : Measure E) i G] with x hx hy
    exact hx.symm.trans ((congrArg (fun w : Lp ℂ 2 (volume : Measure E) => w x) (hd i)).trans hy)
  refine ⟨u,hu,Lp.ext ?_⟩
  let B := EuclideanSpace.basisFun ι ℂ
  filter_upwards [Lp.coeFn_smul cF (grad b u), LpComponents.CM.Construction.lpOrthonormalSynthesis_coe B d,
    hcomp] with x hx hs hcx
  change (cF • grad b u) x = G x
  rw [hx,Pi.smul_apply]
  change cF • LpComponents.CM.Construction.lpOrthonormalSynthesis B d x = G x
  rw [hs,Finset.smul_sum,← B.sum_repr (G x)]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (cF • d i x) • B i := smul_smul cF (d i x) (B i)
    _ = _ := by
      rw [hcx i]
      rfl

theorem sourceEuclideanH1_of_gradient_limits (b : OrthonormalBasis ι ℝ E)
    (M : Lp ℂ 2 (volume : Measure E)) (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (mass : ℕ → Lp ℂ 2 (volume : Measure E))
    (gradient : ℕ → Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hm : Tendsto mass atTop (𝓝 M)) (hg : Tendsto gradient atTop (𝓝 G))
    (hweak : ∀ n i, ∂_{b i} (mass n : 𝓢'(E, ℂ)) = (component i (gradient n) : 𝓢'(E, ℂ))) :
    ∃ u : Lp ℂ 2 (volume : Measure E), J u = M ∧ cF • grad b u = G := by
  apply sourceEuclideanH1_of_weak_gradient b M G
  intro i
  let T := Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2
  let D := LineDeriv.lineDerivOpCLM ℂ 𝓢'(E, ℂ) (b i)
  have hl : Tendsto (fun n => D (T (mass n))) atTop (𝓝 (D (T M))) :=
    (D.continuous.tendsto (T M)).comp ((T.continuous.tendsto M).comp hm)
  have hr : Tendsto (fun n => T (component i (gradient n))) atTop (𝓝 (T (component i G))) :=
    (T.continuous.tendsto (component i G)).comp (((component i).continuous.tendsto G).comp hg)
  have he : (fun n => D (T (mass n))) = fun n => T (component i (gradient n)) :=
    funext fun n => hweak n i
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

end
end ArtinMatthews
