module

public import ArtinMatthews.PrimeExtractionCompositeBounds
public import ArtinMatthews.PrimeExtractionSquarefulGeneral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rough composite sum equals the finite ordered-prime expansion
up to a proved all-logarithmic error. No bilinear cancellation is assumed. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators Asymptotics

noncomputable def roughPositiveUpTo (N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ioc 0 N).filter (MarkedRoughAbove z)

noncomputable def markedCompositeExpansionError {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ roughPositiveUpTo ⌊T * x⌋₊ (x ^ γ), markedExtractionWeight e G Φ x n *
    (actualCompositeThetaCoefficient η χ n -
      roughCompositeCoefficient (fun p => idealThetaCoeff η p * χ p) ⌈2 / γ⌉₊ n (x ^ γ))

theorem markedCompositeExpansionError_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (A : ℝ) :
    markedCompositeExpansionError e η χ G Φ T γ =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  classical
  let b (x : ℝ) (n : ℕ) := actualCompositeThetaCoefficient η χ n -
    roughCompositeCoefficient (fun p => idealThetaCoeff η p * χ p) ⌈2 / γ⌉₊ n (x ^ γ)
  have hb := actualCompositeTheta_expansion_bounds_eventually η χ T hγ
  have hs := markedSquarefulCoefficientSum_isLittleO e he b G hCG hG Φ hΦ hT hγ
    (hb.mono (fun x hx n hn hnT hr => (hx n hn hnT hr).2)) A
  apply hs.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with x hbx hx
  unfold markedSquarefulCoefficientSum markedCompositeExpansionError
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hnrange, hn0, hr, _⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,
      Nat.le_of_lt_succ (Finset.mem_range.mp hnrange)⟩, hr⟩
  · intro n hn hnnot
    obtain ⟨hnI, hr⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := (Finset.mem_Ioc.mp hnI).1.ne'
    have hsq : Squarefree n := by
      by_contra hnsq
      exact hnnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hnI).2), hn0, hr, hnsq⟩)
    have hnT : (n : ℝ) ≤ T * x :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hnI).2).trans (Nat.floor_le (mul_nonneg hT hx.le))
    dsimp only [b]
    rw [(hbx n hn0 hnT hr).1 hsq, sub_self, mul_zero]

noncomputable def markedActualCompositeThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ roughPositiveUpTo ⌊T * x⌋₊ (x ^ γ),
    markedExtractionWeight e G Φ x n * actualCompositeThetaCoefficient η χ n

noncomputable def markedExpandedCompositeThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊T * x⌋₊, markedExtractionWeight e G Φ x n *
    roughCompositeCoefficient (fun p => idealThetaCoeff η p * χ p) ⌈2 / γ⌉₊ n (x ^ γ)

theorem markedCompositeExpansionError_eq {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) :
    markedCompositeExpansionError e η χ G Φ T γ x =
      markedActualCompositeThetaSum e η χ G Φ T γ x -
        markedExpandedCompositeThetaSum e η χ G Φ T γ x := by
  classical
  unfold markedCompositeExpansionError markedActualCompositeThetaSum markedExpandedCompositeThetaSum
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnnot
  have hr : ¬MarkedRoughAbove (x ^ γ) n := fun hr => hnnot (Finset.mem_filter.mpr ⟨hn, hr⟩)
  rw [roughCompositeCoefficient_eq_zero_of_not_rough _ _ _ _ hr, mul_zero]

/-- Genuine composite reduction: squarefree restriction and repeated-prime
exceptions have both been removed with all-logarithmic saving. -/
theorem markedActualCompositeThetaSum_sub_expansion_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (A : ℝ) :
    (fun x => markedActualCompositeThetaSum e η χ G Φ T γ x -
      markedExpandedCompositeThetaSum e η χ G Φ T γ x) =o[atTop]
        (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  apply (markedCompositeExpansionError_isLittleO e he η χ G hCG hG Φ hΦ hT hγ A).congr'
    _ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (markedCompositeExpansionError_eq e η χ G Φ T γ)

end ArtinMatthews
