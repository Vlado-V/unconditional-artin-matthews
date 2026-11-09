module

public import ArtinMatthews.GiantPrimeInvariance
public import ArtinMatthews.GiantProgressionCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded prime coefficient for the literal fixed-residue giant statistic.
It agrees with the original statistic on any fixed compact positive test
support, not just the normalization interval of length two. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology

theorem giantUnitResidueIndicator_norm_le {M : ℕ} (U : Finset (ZMod M)ˣ) (z : ZMod M) :
    ‖giantUnitResidueIndicator U z‖ ≤ 1 := by
  unfold giantUnitResidueIndicator
  split_ifs <;> norm_num

def giantFixedResidueCenteredCoefficient {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε x : ℝ) (u : ℕ) : ℂ :=
  giantUnitResidueIndicator U (u+1 : ℕ) *
    ((boundedGiantIndicator u x ε - giantPrimeReciprocalSum x ε : ℝ) : ℂ)

def giantFixedResidueLiteralCoefficient {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε x : ℝ) (u : ℕ) : ℂ :=
  giantUnitResidueIndicator U (u+1 : ℕ) *
    (((giantPrimeFactors u x ε).card : ℝ) - giantPrimeReciprocalSum x ε : ℝ)

theorem giant_fixed_residue_coefficient_bound {M : ℕ} (U : Finset (ZMod M)ˣ)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖giantFixedResidueCenteredCoefficient U ε x u‖ ≤ 1 := by
  filter_upwards [giantPrimeReciprocalSum_bounds_eventually hε hεq] with x hx
  intro u
  rw [giantFixedResidueCenteredCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (giantUnitResidueIndicator_norm_le U _)
    (boundedGiantIndicator_sub_abs_le_one u x ε _ hx.1 hx.2) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul 1)

theorem giant_threshold_fixed_support (T ε : ℝ) (hε : ε ≤ 1/4) :
    ∀ᶠ x : ℝ in atTop, T*x ≤ (x^(1-ε))^2 := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).eventually
      (eventually_ge_atTop T), eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  calc
    T*x ≤ x*x^(1/2 : ℝ) := by nlinarith
    _ = x^(1+1/2 : ℝ) := by rw [Real.rpow_add hx0, Real.rpow_one]
    _ ≤ x^((1-ε)*2) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ = (x^(1-ε))^2 := by rw [Real.rpow_mul hx0.le, Real.rpow_two]

theorem boundedGiantIndicator_fixed_support (T ε : ℝ) (hε : ε ≤ 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, 0 < u → (u : ℝ) ≤ T*x →
      boundedGiantIndicator u x ε = (giantPrimeFactors u x ε).card := by
  filter_upwards [giant_threshold_fixed_support T ε hε, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro u hu hux
  have hc : (giantPrimeFactors u x ε).card ≤ 1 :=
    (Finset.card_filter_le _ _).trans (card_primeFactorsAbove_le_one hu
      (Real.rpow_nonneg (zero_le_one.trans hx1) _) (hux.trans hx))
  unfold boundedGiantIndicator
  by_cases hempty : (giantPrimeFactors u x ε).Nonempty
  · have hcard : (giantPrimeFactors u x ε).card = 1 := by
      have := Finset.card_pos.mpr hempty
      omega
    simp [hempty,hcard]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]

/-- The fixed-residue coefficient may be capped globally without changing
any tested term on the original compact support. The possible u=0 term is
handled by the original lower support condition. -/
theorem giant_fixed_residue_test_eq {M : ℕ} (U : Finset (ZMod M)ˣ)
    (ε T : ℝ) (hε : ε ≤ 1/4) (hT : 0 ≤ T)
    (Φ : ℝ → ℝ) (hΦzero : Φ 0 = 0) :
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Finset.Icc 0 ⌊T*x⌋₊,
      (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueLiteralCoefficient U ε x u =
        (Φ ((u : ℝ)/x) : ℂ) * giantFixedResidueCenteredCoefficient U ε x u := by
  filter_upwards [boundedGiantIndicator_fixed_support T ε hε, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro u hu
  by_cases hu0 : u=0
  · subst u
    simp only [Nat.cast_zero, zero_div, hΦzero, Complex.ofReal_zero, zero_mul]
  · have hux : (u : ℝ) ≤ T*x :=
      (Nat.le_floor_iff (mul_nonneg hT (zero_le_one.trans hx1))).mp (Finset.mem_Icc.mp hu).2
    rw [giantFixedResidueLiteralCoefficient, giantFixedResidueCenteredCoefficient,
      hx u (Nat.pos_of_ne_zero hu0) hux]

end
end ArtinMatthews
