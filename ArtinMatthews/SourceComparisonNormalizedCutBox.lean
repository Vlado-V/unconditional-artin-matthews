module

public import ArtinMatthews.SourceComparisonBoxCutoff
public import ArtinMatthews.SourceComparisonBoxEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The box cutoff with the original comparison normalization (Y^{-1}). -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

theorem sourceComparisonCutTriple_rescale (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ)
    (ψ : ℝ → ℂ) {Z Y : ℝ} (hZ : 0 < Z) (hY : 0 < Y) (t : ℝ) :
    sourceComparisonCutTriple S c ψ Y Y t =
      ((Z/Y:ℝ):ℂ)*sourceComparisonCutTriple S c ψ Z Y t := by
  have hZC : (Z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hYC : (Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [sourceComparisonCutTriple, sourceComparisonCutTriple, Complex.ofReal_div]
  field_simp

theorem sourceComparison_high_energy_mono_threshold (f : ℝ → ℂ) (hf : Continuous f)
    (T S S' : ℝ) (hS : S ≤ S') :
    (∫ t in sourceComparisonHighTimes T S', ‖f t‖^2) ≤
      ∫ t in sourceComparisonHighTimes T S, ‖f t‖^2 :=
  setIntegral_mono_set ((hf.norm.pow 2).integrableOn_Icc.mono_set (fun _ ht => ht.1))
    (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun _ ht => ⟨ht.1,hS.trans ht.2⟩))

theorem sourceComparisonNormalizedCutBox_high_energy
    (ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : ContDiff ℝ ∞ ψ)
    (D C B A : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (S : Finset (ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ → ℂ) (Z Y T σ : ℝ),
        1 ≤ Z → 0 < Y → Z ≤ b*Y → X^(max 1 C+1) ≤ T → T ≤ Z → Z ≤ Real.exp (3*X) →
        |σ| ≤ X^C →
        (∀ v ∈ S, sourceComparisonTriplePosition v ∈ Finset.Ioc 0 ⌊8*Z⌋₊) →
        (∀ v ∈ S, ‖c v‖ ≤ X^D) →
        (∫ t in sourceComparisonHighTimes (2*T) (X^B),
          ‖sourceComparisonCutTriple S c (fun _ => 1) Z Y t‖^2) ≤ X^(-(A+3)) →
        (∫ t in sourceComparisonHighTimes T (X^(max (max 1 C) B+1)),
          ‖sourceComparisonCutTriple S c ψ Y Y (t+σ)‖^2) ≤ X^(-A) := by
  filter_upwards [sourceComparisonCutTriple_high_energy ψ ha hsupp hψ D C B (A+1) hD (by linarith),
    eventually_ge_atTop (max (1:ℝ) (b^2))] with X hcut hX
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  intro S c Z Y T σ hZ hY hZY hT hTZ hcap hσ hS hc hhigh
  have hs : X^(-(A+3)) = X^(-(A+1)-2) := by congr 1; ring
  have hh := hcut S c Z Y T σ hZ hY hT hTZ hcap hσ hS hc (hs ▸ hhigh)
  simp_rw [sourceComparisonCutTriple_rescale S c ψ (zero_lt_one.trans_le hZ) hY,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Z/Y)]
  rw [integral_const_mul]
  calc
    _ ≤ (Z/Y)^2*X^(-(A+1)) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ ≤ b^2*X^(-(A+1)) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hY).mpr hZY) 2) (by positivity)
    _ ≤ X*X^(-(A+1)) := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hX) (by positivity)
    _ = _ := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]
      congr 1
      ring

end
end ArtinMatthews
