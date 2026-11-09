module

public import ArtinMatthews.PrimeExtractionArithmeticEndpoint


set_option backward.privateInPublic true
@[expose] public section

/-! The original shifted cutoff has finite integer support inside any
fixed larger truncation parameter, for all sufficiently large x. -/

noncomputable section
namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators

theorem markedExtractionWeight_support_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b T : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hbT : b < T) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, markedExtractionWeight e G Φ x n ≠ 0 →
      n ∈ Finset.Ioc 0 ⌊T*x⌋₊ := by
  have hTb : 0 < T-b := sub_pos.mpr hbT
  have hzero : Φ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (hsupp hh).1
  filter_upwards [eventually_ge_atTop (1/(T-b)), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro n hn
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    exact hn (by simp only [markedExtractionWeight, Nat.zero_sub, Nat.cast_zero, zero_div,
      hzero, Complex.ofReal_zero, zero_mul])
  have hcut : Φ (((n-1 : ℕ) : ℝ)/x) ≠ 0 := by
    intro hz
    exact hn (by simp only [markedExtractionWeight, hz, Complex.ofReal_zero, zero_mul])
  have hupper := (div_le_iff₀ hx0).mp (hsupp hcut).2
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one] at hupper
  have hslack : 1 ≤ (T-b)*x := by
    calc
      1 = (T-b)*(1/(T-b)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hTb.le
  exact Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, Nat.le_floor (by linarith)⟩

theorem markedExtractionWeight_tsum_eq_sum_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b T : ℝ}
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hbT : b < T)
    (c : ℝ → ℕ → ℂ) :
    ∀ᶠ x : ℝ in atTop,
      (∑' n : ℕ, markedExtractionWeight e G Φ x n * c x n) =
        ∑ n ∈ Finset.Ioc 0 ⌊T*x⌋₊, markedExtractionWeight e G Φ x n * c x n := by
  filter_upwards [markedExtractionWeight_support_eventually e G Φ ha hsupp hbT] with x hx
  apply tsum_eq_sum
  intro n hn
  have hz : markedExtractionWeight e G Φ x n = 0 := by
    by_contra hh
    exact hn (hx n hh)
  rw [hz, zero_mul]

def markedUnrestrictedRoughThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (γ x : ℝ) : ℂ := by
  classical
  exact ∑' n : ℕ, markedExtractionWeight e G Φ x n *
    (if MarkedRoughAbove (x^γ) n then idealThetaCoeff η n * χ n else 0)

def markedUnrestrictedPrimeThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, markedExtractionWeight e G Φ x n *
    (if n.Prime then idealThetaCoeff η n * χ n else 0)

theorem markedUnrestrictedThetaSum_eq_finite_eventually {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) {a b T : ℝ} (γ : ℝ)
    (ha : 0 < a) (hsupp : Function.support Φ ⊆ Set.Icc a b) (hbT : b < T) :
    ∀ᶠ x : ℝ in atTop,
      markedUnrestrictedRoughThetaSum e η χ G Φ γ x = markedActualRoughThetaSum e η χ G Φ T γ x ∧
        markedUnrestrictedPrimeThetaSum e η χ G Φ x = markedActualPrimeThetaSum e η χ G Φ T x := by
  classical
  filter_upwards [markedExtractionWeight_tsum_eq_sum_eventually e G Φ ha hsupp hbT
      (fun x n => if MarkedRoughAbove (x^γ) n then idealThetaCoeff η n * χ n else 0),
    markedExtractionWeight_tsum_eq_sum_eventually e G Φ ha hsupp hbT
      (fun _ n => if n.Prime then idealThetaCoeff η n * χ n else 0)] with x hr hp
  constructor
  · simpa only [markedUnrestrictedRoughThetaSum, markedActualRoughThetaSum,
      roughPositiveUpTo, Finset.sum_filter, mul_ite, mul_zero] using hr
  · simpa only [markedUnrestrictedPrimeThetaSum, markedActualPrimeThetaSum,
      Finset.sum_filter, mul_ite, mul_zero] using hp

end ArtinMatthews
