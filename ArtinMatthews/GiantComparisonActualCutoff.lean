module

public import ArtinMatthews.GiantComparisonCutoffAggregate
public import ArtinMatthews.GiantComparisonCellBound
public import ArtinMatthews.GiantComparisonFullFamilyArcEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The literal performed comparison branch saves any prescribed
logarithmic power on the global smooth physical cutoff. -/
namespace ArtinMatthews
open Filter Finset
open scoped ContDiff
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantCandidatePerformedComparisonLogSaving_actual
    {I : Type*} [Fintype I] (e : I → ℝ)
    (he : ∀ i, (1/10:ℝ) < e i ∧ e i < 1/5) (hinj : Function.Injective e)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    {M : ℕ} (hm : 0 < M) (χ : DirichletCharacter ℂ M)
    {γ : ℝ} (hγ : 0 < γ) (j : ℕ) (hj : 0 < j)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (Ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : Function.support Ψ ⊆ Set.Icc a b) :
    GiantCandidatePerformedComparisonLogSaving e χ ε γ q j Ψ := by
  let lo := a/2
  let hi := 25*(b+1)+a/2
  let ρ := max (1/2 : ℝ) q
  have hρ : (1/2:ℝ) ≤ ρ := le_max_left _ _
  have hρ1 : ρ < 1 := max_lt (by norm_num) hq1
  have hlo : 0 < lo := by unfold lo; positivity
  have hhi : lo ≤ hi := by dsimp [lo,hi]; linarith
  have hplateau : a < 25*(b+1) := by linarith
  obtain ⟨ψL,ψR,hψL,hψR,hsL,hsR,hreal,hplat⟩ :=
    giantComparisonEndpointCutoffs_exists ha hplateau
  apply giantCandidatePerformedComparisonLogSaving_of_cell_bounds e he hε hεq hm χ hγ j hj
    hq hq1.le Ψ ha hab hΨ hsupp
  intro m E hE
  apply giantCandidateComparisonWeightedCell_log_saving_of_arc e he hε hεq χ hγ j hj
    hq.le hq1.le Ψ ψL ψR ha hab hΨ hsupp hψL hψR hsL hsR hreal hplat m hE
  intro c A hc hA
  filter_upwards [giantComparisonActualArcEnergy_eventually e he hinj (m+1) hρ hρ1
    hε hεq hlo hhi (show hi < hi+1 by linarith) ψL hψL hsL c 2 A hc hA] with x harc
  intro S g t ht ht₀ u hu hbind Y H σ hYlo hYhi hHlo hHhi _ hσ r hr
  let inc : ↥S ↪ GiantCandidateGroupIndex x := ⟨Subtype.val,Subtype.val_injective⟩
  let g₀ := giantCandidatePerformedSplitEquiv S (.inl g)
  have hsmall : inc g₀ = Sum.inl g.val := rfl
  exact harc inc g₀ g.val hsmall t ht ht₀ (fun _ => q)
    (fun _ => ⟨hq.le,le_max_right _ _⟩) u hu hbind Y H σ hYlo hYhi
    (by simpa only [show (38/100:ℝ)=19/50 by norm_num] using hHlo)
    hHhi (by simpa only [Real.rpow_two] using hσ) r hr

end
end ArtinMatthews
