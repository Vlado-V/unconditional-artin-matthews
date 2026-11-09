module

public import ArtinMatthews.CircleThetaErrorRate
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A dilation-uniform detector error for the actual Schwartz source tests. -/

noncomputable section
namespace ArtinMatthews

theorem circleThetaSchwartzSourceError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ F r L : ℕ, 0 < F → 0 < r → F.Coprime r →
      4 * (F*r) ≤ L → ∀ (χ : OAI.SevenEighths.HeckeFamily.Character)
      (m1 m2 T1 T2 : ℕ), 0 < m1 → Squarefree m1 →
      ∀ (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ),
      circleThetaSourceError χ m1 m2 T1 T2 (fun x => W1 (x/K1)) (fun x => W2 (x/K2)) F r L ≤
        C * ((T1 : ℝ)*T2)^2 * (SchwartzMap.seminorm ℝ 0 0 W1) *
          (SchwartzMap.seminorm ℝ 0 0 W2) * (F : ℝ) * (r : ℝ) *
          (((m2 / m1.gcd m2)*T1 + (m1 / m1.gcd m2)*T2 : ℕ) : ℝ)^2 / Real.sqrt L := by
  obtain ⟨C, hC, hbound⟩ := circleThetaSourceError_bound
  refine ⟨C, hC, ?_⟩
  intro F r L hF hr hFr hL χ m1 m2 T1 T2 hm1 hsq W1 W2 K1 K2
  exact hbound F r L hF hr hFr hL χ m1 m2 T1 T2 hm1 hsq
    (fun x => W1 (x/K1)) (fun x => W2 (x/K2))
    (SchwartzMap.seminorm ℝ 0 0 W1) (SchwartzMap.seminorm ℝ 0 0 W2)
    (apply_nonneg _ _) (apply_nonneg _ _)
    (fun _ _ => SchwartzMap.norm_le_seminorm ℝ W1 _)
    (fun _ _ => SchwartzMap.norm_le_seminorm ℝ W2 _)

end ArtinMatthews
