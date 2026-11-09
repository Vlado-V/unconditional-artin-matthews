module

public import ArtinMatthews.PrimeExtractionCompositeBounds
public import ArtinMatthews.PrimeExtractionBoundedError
public import Mathlib.Analysis.Calculus.ContDiff.RCLike


set_option backward.privateInPublic true
@[expose] public section

/-! Shifting the actual smooth cutoff before bilinear reindexing.
The bounded normalized tuple coefficient makes the total shift error O(1). -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators Asymptotics ContDiff

theorem prime_extraction_cutoff_shift_pointwise (Φ : ℝ → ℝ) {K : NNReal}
    (hΦ : LipschitzWith K Φ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    ‖((Φ (((n - 1 : ℕ) : ℝ) / x) - Φ ((n : ℝ) / x) : ℝ) : ℂ)‖ ≤ (K : ℝ) / x := by
  have h := hΦ.norm_sub_le (((n - 1 : ℕ) : ℝ) / x) ((n : ℝ) / x)
  have hd : ((n - 1 : ℕ) : ℝ) / x - (n : ℝ) / x = -1 / x := by
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  rw [hd] at h
  simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos hx] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, one_mul] using h

noncomputable def markedTupleCutoffShift {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊T * x⌋₊,
    ((Φ (((n - 1 : ℕ) : ℝ) / x) - Φ ((n : ℝ) / x) : ℝ) : ℂ) *
      (literalMarkedArrayWeight e x (n - 1) : ℂ) * G x (n - 1) *
        (roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n (x ^ γ) / j.factorial)

theorem markedTupleCutoffShift_bound {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) {K : NNReal} (hΦ : LipschitzWith K Φ) {T : ℝ} (hT : 0 ≤ T)
    (γ : ℝ) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop, ‖markedTupleCutoffShift e η χ G Φ T γ j x‖ ≤
      T * (K : ℝ) * (2 / Real.log 2) ^ Fintype.card ι * CG * (2 : ℝ) ^ j := by
  let W := (2 / Real.log 2) ^ Fintype.card ι
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  filter_upwards [literalMarkedArrayWeight_bound_eventually e he, hG,
    eventually_gt_atTop (0 : ℝ)] with x hW hGx hx
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊T * x⌋₊,
      ‖((Φ (((n - 1 : ℕ) : ℝ) / x) - Φ ((n : ℝ) / x) : ℝ) : ℂ) *
        (literalMarkedArrayWeight e x (n - 1) : ℂ) * G x (n - 1) *
          (roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n (x ^ γ) / j.factorial)‖ ≤
        ((K : ℝ) / x) * W * CG * (2 : ℝ) ^ j := by
    intro n hn
    have hphi := prime_extraction_cutoff_shift_pointwise Φ hΦ hx (Finset.mem_Ioc.mp hn).1
    have hw : ‖(literalMarkedArrayWeight e x (n - 1) : ℂ)‖ ≤ W := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (literalMarkedArrayWeight_nonneg e x (n - 1))] using hW (n - 1)
    have hb : ‖roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n (x ^ γ) /
        j.factorial‖ ≤ (2 : ℝ) ^ j := by
      rw [norm_div, Complex.norm_natCast]
      apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos j : (0 : ℝ) < j.factorial)).mpr
      simpa only [mul_comm] using roughThetaTupleCoefficient_norm_le η χ j n (x ^ γ)
    rw [norm_mul, norm_mul, norm_mul]
    gcongr
    exact hGx _
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊T * x⌋₊,
        ‖((Φ (((n - 1 : ℕ) : ℝ) / x) - Φ ((n : ℝ) / x) : ℝ) : ℂ) *
          (literalMarkedArrayWeight e x (n - 1) : ℂ) * G x (n - 1) *
            (roughPrimeTupleCoefficient (fun p => idealThetaCoeff η p * χ p) j n (x ^ γ) /
              j.factorial)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 ⌊T * x⌋₊, ((K : ℝ) / x) * W * CG * (2 : ℝ) ^ j :=
      Finset.sum_le_sum hterm
    _ = (⌊T * x⌋₊ : ℝ) * (((K : ℝ) / x) * W * CG * (2 : ℝ) ^ j) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
    _ ≤ (T * x) * (((K : ℝ) / x) * W * CG * (2 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (mul_nonneg hT hx.le)) (by positivity)
    _ = _ := by dsimp [W]; field_simp

/-- For the actual normalized theta tuple coefficient and array, the cutoff
shift saves every logarithmic power. Smoothness and compact support supply
the Lipschitz bound, so no shift-error hypothesis remains. -/
theorem markedTupleCutoffShift_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hsupp : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ)
    {T : ℝ} (hT : 0 ≤ T) (γ : ℝ) (j : ℕ) (A : ℝ) :
    markedTupleCutoffShift e η χ G Φ T γ j =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hΦ (by simp)
  exact prime_extraction_bounded_isLittleO _
    (markedTupleCutoffShift_bound e he η χ G hCG hG Φ hK hT γ j) A

end ArtinMatthews
