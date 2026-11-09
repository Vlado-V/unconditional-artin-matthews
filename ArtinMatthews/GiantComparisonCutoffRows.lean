module

public import ArtinMatthews.GiantComparisonCellMellin
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct


set_option backward.privateInPublic true
@[expose] public section

/-! One fixed smooth plateau contains the two physical endpoint ranges
of every logarithmic cell. Its left profile absorbs the actual 1/w. -/
namespace ArtinMatthews
open Filter Finset
open scoped ContDiff Topology ComplexConjugate
noncomputable section

theorem giantComparisonEndpointCutoffs_exists {a B : ℝ} (ha : 0 < a) (hB : a < B) :
    ∃ ψL ψR : ℝ → ℂ,
      ContDiff ℝ ∞ ψL ∧ ContDiff ℝ ∞ ψR ∧
      Function.support ψL ⊆ Set.Icc (a/2) (B+a/2) ∧
      Function.support ψR ⊆ Set.Icc (a/2) (B+a/2) ∧
      (∀ z, conj (ψL z) = ψL z) ∧
      (∀ z ∈ Set.Icc a B, ψL z = (z:ℂ)⁻¹ ∧ ψR z = 1) := by
  let c := (a+B)/2
  let ρ : ContDiffBump c := ⟨(B-a)/2, (B-a)/2+a/2, by linarith, by linarith⟩
  let ψL (z : ℝ) := (ρ z/z : ℝ)
  let ψR (z : ℝ) := (ρ z : ℂ)
  have hρ : ∀ z ∈ Function.support (ρ : ℝ → ℝ), z ∈ Set.Icc (a/2) (B+a/2) := by
    intro z hz
    rw [ρ.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hz
    dsimp only [ρ, c] at hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hψL : ContDiff ℝ ∞ ψL := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq
      have he : ∀ᶠ u in 𝓝 z, u < a/2 := gt_mem_nhds (by linarith)
      filter_upwards [he] with u hu
      have hzero : ρ u = 0 := Function.notMem_support.mp
        (fun hm => (not_le_of_gt hu) (hρ u hm).1)
      simp [ψL, hzero]
    · exact ρ.contDiff.contDiffAt.div contDiffAt_id hz
  refine ⟨fun z => (ψL z : ℂ), ψR, Complex.ofRealCLM.contDiff.comp hψL,
    Complex.ofRealCLM.contDiff.comp ρ.contDiff, ?_, ?_, fun z => Complex.conj_ofReal _, ?_⟩
  · intro z hz
    apply hρ z
    exact fun hn => hz (by simp [ψL, hn])
  · intro z hz
    apply hρ z
    exact fun hn => hz (by simp [ψR, hn])
  · intro z hz
    have hplateau : ρ z = 1 := by
      apply ρ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      dsimp only [ρ,c]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    simp [ψL, ψR, hplateau, one_div]

def giantComparisonCutoffRows (Y lo hi : ℝ) : Finset ℕ :=
  (Ioc 0 ⌊hi*Y⌋₊).filter (fun n => lo*Y ≤ (n:ℝ))

theorem mem_giantComparisonCutoffRows {Y lo hi : ℝ} (hY : 0 < Y) {n : ℕ} :
    n ∈ giantComparisonCutoffRows Y lo hi ↔
      0 < n ∧ (n:ℝ)/Y ∈ Set.Icc lo hi := by
  rw [giantComparisonCutoffRows, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hn, hn'⟩, hlo⟩
    have hny : 0 ≤ hi*Y := by
      by_contra! h
      rw [Nat.floor_of_nonpos h.le] at hn'
      exact (not_le_of_gt hn) hn'
    exact ⟨hn,(le_div_iff₀ hY).2 hlo,
      (div_le_iff₀ hY).2 ((Nat.cast_le.mpr hn').trans (Nat.floor_le hny))⟩
  · rintro ⟨hn,hlo,hhi⟩
    exact ⟨⟨hn,Nat.le_floor ((div_le_iff₀ hY).1 hhi)⟩,(le_div_iff₀ hY).1 hlo⟩

theorem giantComparisonCutoffRows_subset {Y lo hi B : ℝ} (hY : 0 ≤ Y) (hB : hi ≤ B) :
    giantComparisonCutoffRows Y lo hi ⊆ Ioc 0 ⌊B*Y⌋₊ := by
  intro n hn
  obtain ⟨hn₀,hn₁⟩ := mem_Ioc.mp (mem_filter.mp hn).1
  exact mem_Ioc.mpr ⟨hn₀,hn₁.trans (Nat.floor_mono (mul_le_mul_of_nonneg_right hB hY))⟩

end
end ArtinMatthews
