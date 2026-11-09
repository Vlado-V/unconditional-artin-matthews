module

public import ArtinMatthews.ShiftedBilinear
public import ArtinMatthews.CubicThetaShiftedCorrelation
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! The finite weighted theta energy keeps both coefficient conjugates
until the actual coefficient-reality identity is used. -/
namespace ArtinMatthews
open Set Complex
open scoped BigOperators ComplexConjugate
noncomputable section

theorem thetaShiftedCorrelation_eq_weighted_finite
    (χ : OAI.SevenEighths.HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff χ n) = idealThetaCoeff χ n)
    (m1 m2 : ℕ) {T : ℝ} (hT : 1 ≤ T) (g : ℝ → ℝ)
    (hs : Function.support g ⊆ Icc T (2*T)) :
    (∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊,
      (g n : ℂ) * idealThetaCoeff χ (m1*n+1) * conj (idealThetaCoeff χ (m2*n+1))) =
      thetaShiftedCorrelation χ m1 m2 (fun x => (g x : ℂ)) := by
  unfold thetaShiftedCorrelation
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌈2*T⌉₊)]
  · apply Finset.sum_congr rfl
    intro n _
    rw [show conj (idealThetaCoeff χ (m2*n+1)) = idealThetaCoeff χ (m2*n+1) from hreal _]
    ring
  · intro n hn
    have hgn : g n = 0 := by
      by_contra hg
      have hns := hs hg
      have hlo : 1 ≤ n := by exact_mod_cast hT.trans hns.1
      have hhi : n ≤ ⌈2*T⌉₊ := by exact_mod_cast hns.2.trans (Nat.le_ceil (2*T))
      exact hn (Finset.mem_Icc.mpr ⟨hlo,hhi⟩)
    simp only [hgn, Complex.ofReal_zero, mul_zero]

theorem shiftedTheta_weighted_energy_split
    (χ : OAI.SevenEighths.HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff χ n) = idealThetaCoeff χ n)
    (A : Finset ℕ) (α : ℕ → ℂ) (hα : ∀ m ∈ A, ‖α m‖ ≤ 1)
    {T : ℝ} (hT : 1 ≤ T) (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hs : Function.support g ⊆ Icc T (2*T)) :
    (∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊,
      g n * ‖∑ m ∈ A, α m * idealThetaCoeff χ (m*n+1)‖^2) ≤
      (∑ m ∈ A, ∑ n ∈ Finset.Icc 1 ⌈2*T⌉₊,
        g n * ‖idealThetaCoeff χ (m*n+1)‖^2) +
      ∑ p ∈ A.offDiag, ‖thetaShiftedCorrelation χ p.1 p.2 (fun x => (g x : ℂ))‖ := by
  classical
  let range := Finset.Icc 1 ⌈2*T⌉₊
  let corr (m1 m2 : ℕ) := ∑ n ∈ range,
    (g n : ℂ) * idealThetaCoeff χ (m1*n+1) * conj (idealThetaCoeff χ (m2*n+1))
  have henergy :
      (∑ n ∈ range, g n * ‖∑ m ∈ A, α m * idealThetaCoeff χ (m*n+1)‖^2) ≤
        ∑ m1 ∈ A, ∑ m2 ∈ A, ‖corr m1 m2‖ := by
    rw [weighted_bilinear_energy_eq_correlations A range α
      (fun m n => idealThetaCoeff χ (m*n+1)) (fun n => g n)]
    calc
      _ ≤ ‖∑ m1 ∈ A, ∑ m2 ∈ A, α m1 * conj (α m2) * corr m1 m2‖ :=
        Complex.re_le_norm _
      _ ≤ ∑ m1 ∈ A, ∑ m2 ∈ A, ‖α m1 * conj (α m2) * corr m1 m2‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro m1 _
        exact norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m1 hm1
        apply Finset.sum_le_sum
        intro m2 hm2
        simp only [norm_mul, Complex.norm_conj]
        have ha : ‖α m1‖ * ‖α m2‖ ≤ 1 := by
          exact (mul_le_mul (hα m1 hm1) (hα m2 hm2) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (norm_nonneg (corr m1 m2))
  have hdiag (m : ℕ) : ‖corr m m‖ =
      ∑ n ∈ range, g n * ‖idealThetaCoeff χ (m*n+1)‖^2 := by
    have he : corr m m = ((∑ n ∈ range, g n * ‖idealThetaCoeff χ (m*n+1)‖^2 : ℝ) : ℂ) := by
      dsimp only [corr]
      push_cast
      apply Finset.sum_congr rfl
      intro n _
      rw [← Complex.mul_conj']
      ring
    have hnonneg : 0 ≤ ∑ n ∈ range, g n * ‖idealThetaCoeff χ (m*n+1)‖^2 :=
      Finset.sum_nonneg (fun n _ => mul_nonneg (hg n) (sq_nonneg _))
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    _ ≤ ∑ m1 ∈ A, ∑ m2 ∈ A, ‖corr m1 m2‖ := henergy
    _ = _ := by
      rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
        Finset.sum_union (Finset.disjoint_diag_offDiag A), Finset.sum_diag]
      congr 1
      · exact Finset.sum_congr rfl (fun m _ => hdiag m)
      · apply Finset.sum_congr rfl
        intro p _
        exact congrArg norm (thetaShiftedCorrelation_eq_weighted_finite χ hreal p.1 p.2 hT g hs)

end
end ArtinMatthews
