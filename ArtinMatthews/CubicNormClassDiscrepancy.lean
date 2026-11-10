module

public import ArtinMatthews.CubicNormClassIdealReindex
public import ArtinMatthews.CubicNormCellDiscrepancy
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Order.CompletePartialOrder


set_option backward.privateInPublic true
@[expose] public section

/-! The actual shifted norm-class estimate (6.6), uniform in the moving
congruence modulus and every residue class. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators ContDiff

theorem giantCubicNormClassSum_bound (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Ioo 1 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ (b : ZMod q) (x : ℝ), 1 ≤ x →
      ‖giantCubicNormClassSum (cubicNumeratorHeckeCharacter A hA) χ b Φ x‖ ≤
        C * ((q : ℝ) * Real.sqrt x + (q : ℝ) ^ 2) := by
  have hc : HasCompactSupport Φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hs.trans Set.Ioo_subset_Icc_self)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hΦ (by simp)
  let M₀ := (9 * A).natAbs * M
  have hM₀ : 0 < M₀ :=
    Nat.mul_pos (Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hA)) (NeZero.pos M)
  let C₁ := 2187 * (L : ℝ) * (M₀ : ℝ)
  let C₂ := 49 * (L : ℝ) * (M₀ : ℝ) ^ 2
  let C := 1 + C₁ + C₂
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro q hq b x hx
  let P := M₀ * q
  let : NeZero P := ⟨Nat.ne_of_gt (Nat.mul_pos hM₀ hq)⟩
  have hAdiv : 9 * A ∣ (P : ℤ) := by
    dsimp only [P, M₀]
    push_cast
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (self_dvd_abs (9 * A)) _) _
  have hMdiv : M ∣ P := dvd_mul_of_dvd_left (dvd_mul_left M (9 * A).natAbs) q
  have hqdiv : q ∣ P := dvd_mul_left q M₀
  let η := cubicNumeratorHeckeCharacter A hA
  let w := cubicNormClassResidueWeight η χ b P
  have hw (r : Fin P × Fin P) : ‖w r‖ ≤ 1 := cubicNormClassWeight_norm_le η χ b _
  have hzero : ∑ r, w r = 0 :=
    cubicNormClassResidueWeight_sum_zero A hA hnoncube χ b hAdiv hMdiv hqdiv
  have hEq : 6 * giantCubicNormClassSum η χ b Φ x = cubicNormSmoothLatticeSum w Φ x := by
    rw [giantCubicNormClassSum_six_eq_lattice η χ b Φ hs hx]
    unfold cubicNormSmoothLatticeSum
    apply tsum_congr
    intro z
    rw [cubicNormClassResidueWeight_periodic A hA χ b hAdiv hMdiv hqdiv]
  have hb := cubicNormSmoothLatticeSum_norm_le w hw hzero Φ hs hL hx
  rw [← hEq, norm_mul, show ‖(6 : ℂ)‖ = 6 by norm_num] at hb
  calc
    _ ≤ 6 * ‖giantCubicNormClassSum η χ b Φ x‖ := by
      linarith [norm_nonneg (giantCubicNormClassSum η χ b Φ x)]
    _ ≤ 2187 * (L : ℝ) * (P : ℝ) * Real.sqrt x + 49 * (L : ℝ) * (P : ℝ) ^ 2 := hb
    _ = C₁ * ((q : ℝ) * Real.sqrt x) + C₂ * (q : ℝ) ^ 2 := by
      dsimp only [P, C₁, C₂]
      push_cast
      ring
    _ ≤ C * ((q : ℝ) * Real.sqrt x) + C * (q : ℝ) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (by positivity))
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (by positivity))
    _ = _ := by ring

end ArtinMatthews
