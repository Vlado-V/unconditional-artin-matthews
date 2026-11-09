module

public import ArtinMatthews.CubicNormClassDiscrepancy
public import ArtinMatthews.GiantSamplingCofactors
public import ArtinMatthews.MarkedProgressionCounting


set_option backward.privateInPublic true
@[expose] public section

/-! A retained marking divisor and the actual shifted divisibility gate give
one norm class modulo their product. Noncoprime gates have empty support. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators ContDiff

def giantCubicSamplingBaselineSum (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (x : ℝ) (r : ℕ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, H u * giantCubicSamplingKernel η χ Φ x r u

def giantCubicSamplingDivisorBaseline (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) (x : ℝ) (d r : ℕ) : ℂ :=
  giantCubicSamplingBaselineSum η χ (fun u => if d ∣ u then 1 else 0) Φ x r

theorem giantCubicSamplingDivisorBaseline_eq_zero (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) (x : ℝ) {d r : ℕ}
    (hcop : ¬ d.Coprime r) :
    giantCubicSamplingDivisorBaseline η χ Φ x d r = 0 := by
  unfold giantCubicSamplingDivisorBaseline giantCubicSamplingBaselineSum
  apply Finset.sum_eq_zero
  intro u _hu
  by_cases hd : d ∣ u
  · have hru : ¬ r ∣ u + 1 := fun h => hcop (marked_divisor_coprime hd h)
    simp only [ite_eq_left hd, giantCubicSamplingKernel, ite_eq_right hru, mul_zero]
  · simp only [ite_eq_right hd, zero_mul]

theorem giantCubicSamplingDivisorBaseline_eq_normClass (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    {x : ℝ} (hx : 1 ≤ x) {d r : ℕ} (hd : 0 < d) (hr : 0 < r) (hcop : d.Coprime r) :
    ∃ b : ZMod (d * r),
      giantCubicSamplingDivisorBaseline η χ Φ x d r = giantCubicNormClassSum η χ b Φ x := by
  obtain ⟨a, _ha, hcrt⟩ := marked_divisor_crt hd hr hcop
  let b : ZMod (d * r) := ((a + 1 : ℕ) : ZMod (d * r))
  have hgate (u : ℕ) : (d ∣ u ∧ r ∣ u + 1) ↔ ((u + 1 : ℕ) : ZMod (d * r)) = b := by
    dsimp only [b]
    rw [ZMod.natCast_eq_natCast_iff]
    exact (hcrt u).trans ⟨fun h => h.add_right 1, Nat.ModEq.add_right_cancel' 1⟩
  refine ⟨b, ?_⟩
  let N := ⌊2 * x⌋₊
  let F (n : ℕ) : ℂ :=
    if (n : ZMod (d * r)) = b then
      idealThetaCoeff η n * χ n * (Φ (((n : ℝ) - 1) / x) : ℂ)
    else 0
  have hΦ₀ : Φ 0 = 0 := by
    by_contra h
    exact (by norm_num : ¬ (1 : ℝ) < 0) (hs h).1
  have hF₁ : F 1 = 0 := by simp [F, hΦ₀]
  unfold giantCubicSamplingDivisorBaseline giantCubicSamplingBaselineSum giantCubicNormClassSum
  change (∑ u ∈ Finset.Icc 1 N, _) = ∑ n ∈ Finset.Icc 1 ⌊2 * x + 1⌋₊, F n
  rw [Nat.floor_add_one (by positivity : 0 ≤ 2 * x)]
  calc
    _ = ∑ n ∈ Finset.Icc 2 (N + 1), F n := by
      apply Finset.sum_bij (fun u _ => u + 1)
      · intro u hu
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hu
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro u _hu v _hv h
        omega
      · intro n hn
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
        exact ⟨n - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro u _hu
        dsimp only [F]
        have hu : ((u + 1 : ℕ) : ℝ) - 1 = (u : ℝ) := by
          push_cast
          ring
        rw [hu]
        by_cases hdu : d ∣ u <;> by_cases hru : r ∣ u + 1
        · rw [ite_eq_left hdu, one_mul, giantCubicSamplingKernel, ite_eq_left hru,
            ite_eq_left ((hgate u).mp ⟨hdu, hru⟩)]
          push_cast
          ring
        · simp only [ite_eq_left hdu, one_mul, giantCubicSamplingKernel, ite_eq_right hru,
            ite_eq_right (fun h => hru ((hgate u).mpr h).2)]
        · simp only [ite_eq_right hdu, zero_mul, ite_eq_right (fun h => hdu ((hgate u).mpr h).1)]
        · simp only [ite_eq_right hdu, zero_mul, ite_eq_right (fun h => hdu ((hgate u).mpr h).1)]
    _ = _ := by
      apply Finset.sum_subset
      · intro n hn
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨by omega, h₂⟩
      · intro n hn hnot
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
        have he : n = 1 := by
          by_contra hne
          exact hnot (Finset.mem_Icc.mpr ⟨by omega, h₂⟩)
        simpa only [he] using hF₁

theorem giantCubicSamplingDivisorBaseline_norm_le (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Ioo 1 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 1 ≤ x → ∀ (d r : ℕ), 0 < d → 0 < r →
      ‖giantCubicSamplingDivisorBaseline (cubicNumeratorHeckeCharacter A hA) χ Φ x d r‖ ≤
        C * (((d * r : ℕ) : ℝ) * Real.sqrt x + ((d * r : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := giantCubicNormClassSum_bound A hA hnoncube χ Φ hΦ hs
  refine ⟨C, hC, ?_⟩
  intro x hx d r hd hr
  by_cases hc : d.Coprime r
  · obtain ⟨b, he⟩ := giantCubicSamplingDivisorBaseline_eq_normClass
      (cubicNumeratorHeckeCharacter A hA) χ Φ hs hx hd hr hc
    rw [he]
    exact hb (d * r) (Nat.mul_pos hd hr) b x hx
  · rw [giantCubicSamplingDivisorBaseline_eq_zero _ χ Φ x hc, norm_zero]
    positivity

end ArtinMatthews
