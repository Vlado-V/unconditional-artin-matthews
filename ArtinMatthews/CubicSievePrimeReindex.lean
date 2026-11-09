module

public import ArtinMatthews.CubicSieveMarkedPrimeBound
public import ArtinMatthews.MarkedCorrelationEndpoint


set_option backward.privateInPublic true
@[expose] public section

/-! Exact predecessor reindexing and removal of the actual marking arrays
from the centered cubic prime statistic. -/

noncomputable section
namespace ArtinMatthews

open Filter Finset OAI OAI.SevenEighths
open scoped BigOperators ContDiff Topology Asymptotics

def giantCubicCenteredPrimeCoefficient (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (ε x : ℝ) (u : ℕ) : ℂ :=
  giantMarkedCenteredCore ε x u * idealThetaCoeff η (u + 1) * χ (u + 1)

theorem cubicSieve_prime_predecessor_sum (H : ℕ → ℂ) (Φ : ℝ → ℝ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ (Ioc 0 ⌊3 * x⌋₊).filter Nat.Prime,
      (Φ (((p - 1 : ℕ) : ℝ) / x) : ℂ) * H (p - 1)) =
    ∑ u ∈ (Icc 0 ⌊2 * x⌋₊).filter (fun u => (u + 1).Prime), (Φ ((u : ℝ) / x) : ℂ) * H u := by
  let U := (Icc 0 ⌊2 * x⌋₊).filter (fun u => (u + 1).Prime)
  let P := (Icc 1 (⌊2 * x⌋₊ + 1)).filter Nat.Prime
  let Q := (Ioc 0 ⌊3 * x⌋₊).filter Nat.Prime
  let f (p : ℕ) := (Φ (((p - 1 : ℕ) : ℝ) / x) : ℂ) * H (p - 1)
  have hx₀ := zero_lt_one.trans_le hx
  have hshift : (∑ u ∈ U, (Φ ((u : ℝ) / x) : ℂ) * H u) = ∑ p ∈ P, f p := by
    apply sum_bij (fun u _ => u + 1)
    · intro u hu
      obtain ⟨hu, hp⟩ := mem_filter.mp hu
      obtain ⟨hu₀, huN⟩ := mem_Icc.mp hu
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hp⟩
    · intro u _ v _ h
      omega
    · intro p hp
      obtain ⟨hp, hprime⟩ := mem_filter.mp hp
      obtain ⟨hp₁, hpN⟩ := mem_Icc.mp hp
      refine ⟨p - 1, mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, ?_⟩, by omega⟩
      simpa only [Nat.sub_add_cancel hp₁] using hprime
    · intro u _
      simp only [f, Nat.add_sub_cancel]
  have hcap : ⌊2 * x⌋₊ + 1 ≤ ⌊3 * x⌋₊ := by
    apply Nat.le_floor
    have h := Nat.floor_le (show 0 ≤ 2 * x by positivity)
    push_cast
    linarith
  have hsub : P ⊆ Q := by
    intro p hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    obtain ⟨hp₁, hpN⟩ := mem_Icc.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpN.trans hcap⟩, hprime⟩
  have heq : (∑ p ∈ P, f p) = ∑ p ∈ Q, f p := by
    apply sum_subset hsub
    intro p hp hn
    by_contra hf
    have hφ : Φ (((p - 1 : ℕ) : ℝ) / x) ≠ 0 := by
      intro hz
      exact hf (by simp only [f, hz, Complex.ofReal_zero, zero_mul])
    have hpred : p - 1 ≤ ⌊2 * x⌋₊ := Nat.le_floor ((div_lt_iff₀ hx₀).mp (hs hφ).2).le
    obtain ⟨_, hprime⟩ := mem_filter.mp hp
    exact hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.one_lt.le, by omega⟩, hprime⟩)
  exact heq.symm.trans hshift.symm

theorem cubicSieve_actual_prime_eq_correlation {J : Type*} [Fintype J]
    (e : J → ℝ) (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x) :
    markedActualPrimeThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 x =
      ∑ u ∈ (Icc 0 ⌊2 * x⌋₊).filter (fun u => (u + 1).Prime),
        (Φ ((u : ℝ) / x) : ℂ) * giantCubicCenteredPrimeCoefficient η χ ε x u *
          (literalMarkedArrayWeight e x u : ℂ) := by
  let H (u : ℕ) := giantCubicCenteredPrimeCoefficient η χ ε x u * (literalMarkedArrayWeight e x u : ℂ)
  calc
    _ = ∑ p ∈ (Ioc 0 ⌊3 * x⌋₊).filter Nat.Prime,
        (Φ (((p - 1 : ℕ) : ℝ) / x) : ℂ) * H (p - 1) := by
      unfold markedActualPrimeThetaSum markedExtractionWeight
      apply sum_congr rfl
      intro p hp
      have hp₁ : 1 ≤ p := (mem_filter.mp hp).2.one_lt.le
      dsimp only [H, giantCubicCenteredPrimeCoefficient]
      simp only [Nat.sub_add_cancel hp₁, Nat.cast_sub hp₁, Nat.cast_one, sub_add_cancel]
      ring
    _ = ∑ u ∈ (Icc 0 ⌊2 * x⌋₊).filter (fun u => (u + 1).Prime),
        (Φ ((u : ℝ) / x) : ℂ) * H u := cubicSieve_prime_predecessor_sum H Φ hs hx
    _ = _ := sum_congr rfl (fun _ _ => by dsimp only [H]; ring)

theorem cubicSieve_singleArray_correlation_eq {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x) :
    markedPrimeSingleArrayCorrelation e Φ 2 (giantCubicCenteredPrimeCoefficient η χ ε) x =
      (((literalMarkedArrayMean e x)⁻¹ : ℝ) : ℂ) *
        markedActualPrimeThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 x := by
  rw [cubicSieve_actual_prime_eq_correlation e η χ ε Φ hs hx]
  unfold markedPrimeSingleArrayCorrelation literalMarkedArrayMean literalMarkedArrayWeight
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  simp only [Complex.ofReal_div, Complex.ofReal_inv]
  ring

theorem cubicSieve_singleArray_correlation_norm {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (η : HeckeFamily.Character) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (ε : ℝ) (Φ : ℝ → ℝ) (hs : Function.support Φ ⊆ Set.Ioo 1 2) {x : ℝ} (hx : 1 ≤ x)
    (hW : 0 < literalMarkedArrayMean e x) :
    Real.log x / x * ‖markedPrimeSingleArrayCorrelation e Φ 2 (giantCubicCenteredPrimeCoefficient η χ ε) x‖ =
      cubicSieveNormalizedScale e x *
        ‖markedActualPrimeThetaSum e η χ (giantMarkedCenteredCore ε) Φ 3 x‖ := by
  rw [cubicSieve_singleArray_correlation_eq e η χ ε Φ hs hx, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW)]
  unfold cubicSieveNormalizedScale
  ring

theorem giantCubicCenteredPrimeCoefficient_bound (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1 / 4) :
    ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, (u + 1).Prime →
      ‖giantCubicCenteredPrimeCoefficient η χ ε x u‖ ≤ 2 := by
  filter_upwards [giantPrimeReciprocalSum_bounds_eventually hε hεq] with x hx
  intro u hp
  have hcore : ‖giantMarkedCenteredCore ε x u‖ ≤ 1 := by
    simpa only [giantMarkedCenteredCore, Complex.norm_real, Real.norm_eq_abs] using
      boundedGiantIndicator_sub_abs_le_one u x ε _ hx.1 hx.2
  unfold giantCubicCenteredPrimeCoefficient
  rw [norm_mul, norm_mul]
  exact (mul_le_mul (mul_le_mul hcore (idealThetaCoeff_prime_norm_le_two η hp)
      (norm_nonneg _) zero_le_one) (χ.norm_le_one _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

end ArtinMatthews
