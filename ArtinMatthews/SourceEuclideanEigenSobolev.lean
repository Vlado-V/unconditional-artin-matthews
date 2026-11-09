module

public import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! Nested cutoff induction for a weak equation with a smooth zeroth-order
multiplier of the solution. The localized forcing gains its Sobolev
order from the solution on the larger cutoff. -/

namespace ArtinMatthews

open MeasureTheory TemperedDistribution Set Filter
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped SchwartzMap ContDiff Topology

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

local notation "J" => SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
local notation "cut" => SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1
local notation "mulL2" => CutoffDifferential.CM.Construction.schwartzL2Multiply
local notation "grad" => EuclideanGradient.CM.Construction.sobolevVectorGradient

omit [Fintype ι] in
theorem sourceEigen_cutoff_forcing_inner (m g η : 𝓢(E, ℂ))
    (hη : ∀ x ∈ tsupport g, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u v : Lp ℂ 2 (volume : Measure E)) :
    inner ℝ (mulL2 m (J (cut η u))) (J (cut g v)) =
      inner ℝ (mulL2 m (J u)) (J (cut g v)) := by
  rw [CutoffDifferential.CM.Construction.sobolevCutoffCLM_embedding η u,
    CutoffDifferential.CM.Construction.sobolevCutoffCLM_embedding g v]
  change (∫ x, inner ℝ (mulL2 m (mulL2 η (J u)) x) (mulL2 g (J v) x)) =
    ∫ x, inner ℝ (mulL2 m (J u) x) (mulL2 g (J v) x)
  apply integral_congr_ae
  filter_upwards [CutoffDifferential.CM.Construction.schwartzL2Multiply_coe m (mulL2 η (J u)),
    CutoffDifferential.CM.Construction.schwartzL2Multiply_coe η (J u),
    CutoffDifferential.CM.Construction.schwartzL2Multiply_coe m (J u),
    CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (J v)] with x hm hηu hm' hg
  by_cases hx : g x = 0
  · simp only [hg, hx, zero_smul, inner_zero_right]
  · have hηx : η x = 1 := (hη x ((subset_tsupport g) hx)).eq_of_nhds
    rw [hm, hηu, hηx, one_smul, hm']

theorem sourceLocalEigen_all_orders
    (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    {U : Set E} (hU : IsOpen U) (u : Lp ℂ 2 (volume : Measure E)) (m : 𝓢(E, ℂ))
    (hsol : LocalSmoothRegularity.CM.Construction.IsLocalEuclideanWeakMetricSolution b A U u (mulL2 m (J u)))
    (n : ℕ) (g : 𝓢(E, ℂ)) (hgc : HasCompactSupport (g : E → ℂ))
    (hgreal : ∀ x, g x = Complex.ofReal (g x).re) (hgU : tsupport g ⊆ U) :
    MemSobolev ((n : ℝ) + 1) 2 (J (cut g u) : 𝓢'(E, ℂ)) := by
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    rw [SobolevIs.CM.Construction.sobolevL2Embedding_distribution,
      memSobolev_besselPotential_iff, neg_add_cancel]
    exact memSobolev_zero_iff.mpr ⟨cut g u,rfl⟩
  | succ n ih =>
    obtain ⟨η,hηc,hηU,hηreal,hηg⟩ :=
      NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hgc hU hgU
    let uη := cut η u
    let fη := mulL2 m (J uη)
    have hηreg : MemSobolev ((n : ℝ)+1) 2 (J uη : 𝓢'(E, ℂ)) := ih η hηc hηreal hηU
    have hfη : MemSobolev (n : ℝ) 2 (fη : 𝓢'(E, ℂ)) := by
      change MemSobolev (n : ℝ) 2 (mulL2 m (J uη) : 𝓢'(E, ℂ))
      rw [CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution]
      exact SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff n m (hηreg.mono (by linarith))
    have hlocal (v : Lp ℂ 2 (volume : Measure E)) :
        (∫ x, inner ℝ (A x (grad b uη x)) (grad b (cut g v) x)) = inner ℝ fη (J (cut g v)) :=
      (NestedCutoffIdentities.CM.Construction.nested_cutoff_energy_eq b A g η hηg u v).trans
        ((hsol g hgc hgreal hgU v).trans (sourceEigen_cutoff_forcing_inner m g η hηg u v).symm)
    have hgain := HigherCutoffRegularity.CM.Construction.local_elliptic_cutoff_regularity
      b n A c hA hc hL hC ha hpos g hgreal uη fη hlocal hηreg hfη
    change MemSobolev ((n : ℝ)+2) 2 (J (cut g (cut η u)) : 𝓢'(E, ℂ)) at hgain
    rw [NestedCutoffIdentities.CM.Construction.sobolevCutoffCLM_nested 1 g η hηg u] at hgain
    simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using hgain

theorem sourceLocalEigen_smooth_near_point
    (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    {U : Set E} (hU : IsOpen U) (u : Lp ℂ 2 (volume : Measure E)) (m : 𝓢(E, ℂ))
    (hsol : LocalSmoothRegularity.CM.Construction.IsLocalEuclideanWeakMetricSolution b A U u (mulL2 m (J u)))
    {x : E} (hx : x ∈ U) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∃ v : BoundedContinuousFunction E ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ) ∧
        (v : E → ℂ) =ᵐ[(volume : Measure E).restrict W] J u := by
  obtain ⟨g,hgc,hgU,hgreal,hgx⟩ :=
    NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
      (isCompact_singleton (x := x)) hU (singleton_subset_iff.mpr hx)
  have horders (n : ℕ) : MemSobolev (n : ℝ) 2 (J (cut g u) : 𝓢'(E, ℂ)) :=
    (sourceLocalEigen_all_orders b A c hA hc hL hC ha hpos hU u m hsol n g hgc hgreal hgU).mono (by linarith)
  obtain ⟨v,hv,hsmooth⟩ := Smooth.CM.Construction.sobolev_all_orders_smooth horders
  have hW : U ∩ {y | g y = 1} ∈ 𝓝 x := inter_mem (hU.mem_nhds hx) (hgx x (mem_singleton x))
  obtain ⟨W,hWW,hWo,hxW⟩ := mem_nhds_iff.mp hW
  refine ⟨W,hWo,hxW,fun _ hy => (hWW hy).1,v,hsmooth,(ae_restrict_iff' hWo.measurableSet).mpr ?_⟩
  have hvae := Smooth.CM.Construction.boundedFunctionDistribution_eq_lp_ae v _ hv
  rw [CutoffDifferential.CM.Construction.sobolevCutoffCLM_embedding g u] at hvae
  filter_upwards [hvae, CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (J u)] with y hy hmul
  intro hyW
  rw [hy, hmul, (hWW hyW).2, one_smul]

end
end ArtinMatthews
