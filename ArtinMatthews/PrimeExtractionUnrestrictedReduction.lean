module

public import ArtinMatthews.PrimeExtractionUnrestrictedSupport


set_option backward.privateInPublic true
@[expose] public section

/-! The original unrestricted arithmetic sums, for a smooth cutoff
compactly supported in (0,infinity), reduced to actual marked phase sums. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators ContDiff Asymptotics

theorem prime_extraction_compact_positive_support_bounds (Φ : ℝ → ℝ)
    (hcompact : HasCompactSupport Φ) (hpos : tsupport Φ ⊆ Set.Ioi 0) :
    ∃ a b T : ℝ, 0 < a ∧ 0 < T ∧ b < T ∧ Function.support Φ ⊆ Set.Icc a b := by
  obtain ⟨a, ha, hamin⟩ := hcompact.isCompact.exists_forall_le'
    (continuous_id.continuousOn : ContinuousOn (fun y : ℝ => y) (tsupport Φ))
    (fun y hy => hpos hy)
  obtain ⟨b, hb⟩ := hcompact.isCompact.bddAbove
  refine ⟨a, b, max b 0 + 1, ha, by linarith [le_max_right b (0 : ℝ)],
    by linarith [le_max_left b (0 : ℝ)], ?_⟩
  intro y hy
  exact ⟨hamin y (subset_tsupport Φ hy), hb (subset_tsupport Φ hy)⟩

theorem markedUnrestrictedThetaSum_mellin_reduction_of_support
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) {a b T γ : ℝ} (ha : 0 < a) (hT : 0 ≤ T) (hbT : b < T)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hsupp : Function.support Φ ⊆ Set.Icc a b)
    (hΦ : ContDiff ℝ ∞ Φ) (A : ℝ) :
    let hsuppT : Function.support Φ ⊆ Set.Icc a T :=
      fun _ hy => ⟨(hsupp hy).1, (hsupp hy).2.trans hbT.le⟩
    (fun x => markedUnrestrictedRoughThetaSum e η χ G Φ γ x -
      markedUnrestrictedPrimeThetaSum e η χ G Φ x -
        ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
          markedExtractionRelevantMellin e η χ G Φ ha hsuppT hΦ γ j (Real.log x) x) =o[atTop]
            (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  dsimp only
  apply (markedActualRoughThetaSum_sub_prime_mellin_reduction
    e he η χ G hCG hG Φ ha hT hγ hγ1
      (fun _ hy => ⟨(hsupp hy).1, (hsupp hy).2.trans hbT.le⟩) hΦ A).congr'
    _ Filter.EventuallyEq.rfl
  filter_upwards [markedUnrestrictedThetaSum_eq_finite_eventually e η χ G Φ γ ha hsupp hbT]
    with x hx
  rw [hx.1, hx.2]

/-- Original cutoff quantifiers: every smooth real cutoff compactly
supported inside (0,infinity) admits fixed positive box-scale constants.
The original unrestricted sums are reduced with every logarithmic saving. -/
theorem markedUnrestrictedThetaSum_mellin_reduction
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hcompact : HasCompactSupport Φ) (hpos : tsupport Φ ⊆ Set.Ioi 0)
    (hΦ : ContDiff ℝ ∞ Φ) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ (a T : ℝ) (ha : 0 < a), 0 < T ∧
      ∃ hsupp : Function.support Φ ⊆ Set.Icc a T, ∀ A : ℝ,
        (fun x => markedUnrestrictedRoughThetaSum e η χ G Φ γ x -
          markedUnrestrictedPrimeThetaSum e η χ G Φ x -
            ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊,
              markedExtractionRelevantMellin e η χ G Φ ha hsupp hΦ γ j (Real.log x) x) =o[atTop]
                (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  obtain ⟨a, b, T, ha, hT, hbT, hsupp⟩ :=
    prime_extraction_compact_positive_support_bounds Φ hcompact hpos
  refine ⟨a, T, ha, hT, (fun _ hy => ⟨(hsupp hy).1, (hsupp hy).2.trans hbT.le⟩), ?_⟩
  intro A
  exact markedUnrestrictedThetaSum_mellin_reduction_of_support
    e he η χ G hCG hG Φ ha hT.le hbT hγ hγ1 hsupp hΦ A

end ArtinMatthews
