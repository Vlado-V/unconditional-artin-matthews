module

public import ArtinMatthews.SpectralNativeMultiplierIdentification
public import ArtinMatthews.SpectralKLCompactOrder


set_option backward.privateInPublic true
@[expose] public section

/-! The actual native height coefficient is the literal physical
K transform, with its positive-height support retained. -/

noncomputable section
open Set MeasureTheory OAI.CubicEisenstein
open scoped MatrixGroups
namespace ArtinMatthews

theorem spectralKLHeightPhysicalTest_nonpos {q : ℝ} (hq : 0 < q)
    (ρ : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    spectralKLHeightPhysicalTest q ρ x = 0 := by
  have hs : Real.sqrt (x/q) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hq.le)
  simp [spectralKLHeightPhysicalTest,spectralKLHeightBaseTest,hs]

theorem gamma0NativeOrderTransform_eq_physical (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (ρ : ℝ → ℝ) (F : ℝ → ℂ)
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0)
    (hphysical : ∀ x : ℝ, 0 < x →
      spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
        (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) x = F x) (ν : ℂ) :
    gamma0NativeOrderTransform N r n ρ ν = spectralKLCompactOrderTransform F ν := by
  symm
  unfold spectralKLCompactOrderTransform
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))
    (fun x hx => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv]
    rw [hphysical x hx]
  · simp [spectralKLCompactOrderIntegrand,spectralKLPhysicalCompactDiv,
      hzero x (le_of_not_gt hx)]

theorem gamma0NativeOrderTransform_eq_compactOrder (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (ρ : ℝ → ℝ) (ν : ℂ) :
    gamma0NativeOrderTransform N r n ρ ν = spectralKLCompactOrderTransform
      (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
        (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) ν := by
  apply gamma0NativeOrderTransform_eq_physical
  · exact fun x hx => spectralKLHeightPhysicalTest_nonpos
      (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)) _ hx
  · exact fun _ _ => rfl

end ArtinMatthews
