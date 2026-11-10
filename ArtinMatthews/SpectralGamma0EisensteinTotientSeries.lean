module

public import ArtinMatthews.SpectralGamma0EisensteinPositiveCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine absolute convergence of the scattering totient Dirichlet series. -/
noncomputable section
namespace ArtinMatthews

def gamma0EisensteinTotientSeries (N : ℕ) (s : ℂ) : ℂ :=
  ∑' c : {c : ℕ // 0<c ∧ N∣c}, (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)

theorem gamma0EisensteinTotientTerm_norm_bound (N : ℕ) (s : ℂ)
    (c : {c : ℕ // 0<c ∧ N∣c}) :
    ‖(c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)‖ ≤ (c.val:ℝ)^(1-2*s.re) := by
  have hc : 0<(c.val:ℝ) := by exact_mod_cast c.property.1
  rw [norm_mul,Complex.norm_natCast,Complex.norm_natCast_cpow_of_pos c.property.1]
  have hre : (-2*s).re= -2*s.re := by simp
  rw [hre]
  calc
    _ ≤ (c.val:ℝ)*(c.val:ℝ)^(-2*s.re) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.totient_le c.val) (Real.rpow_nonneg hc.le _)
    _ = _ := by
      calc
        _ = (c.val:ℝ)^1*(c.val:ℝ)^(-2*s.re) := by rw [Real.rpow_one]
        _ = (c.val:ℝ)^(1+(-2*s.re)) := (Real.rpow_add hc _ _).symm
        _ = _ := by congr 1; ring

theorem gamma0EisensteinTotientSeries_summable_norm (N : ℕ) (s : ℂ) (hs : 1<s.re) :
    Summable (fun c : {c : ℕ // 0<c ∧ N∣c} => ‖(c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)‖) :=
  ((Real.summable_nat_rpow.mpr (by linarith : 1-2*s.re< -1)).subtype
    (fun c : ℕ => 0<c ∧ N∣c)).of_nonneg_of_le (fun _ => norm_nonneg _)
      (gamma0EisensteinTotientTerm_norm_bound N s)

theorem gamma0EisensteinTotientSeries_summable (N : ℕ) (s : ℂ) (hs : 1<s.re) :
    Summable (fun c : {c : ℕ // 0<c ∧ N∣c} => (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)) :=
  (gamma0EisensteinTotientSeries_summable_norm N s hs).of_norm

def gamma0EisensteinPositiveFirstDivisibilityEquiv (N : ℕ) :
    Gamma0EisensteinPositiveFirst N ≃ {c : ℕ // 0<c ∧ N∣c} where
  toFun c := ⟨c.val,c.property.1,(ZMod.natCast_eq_zero_iff c.val N).mp c.property.2⟩
  invFun c := ⟨c.val,c.property.1,(ZMod.natCast_eq_zero_iff c.val N).mpr c.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem gamma0EisensteinTotientSeries_eq_positive_first (N : ℕ) (s : ℂ) :
    (∑' c : Gamma0EisensteinPositiveFirst N, (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)) =
      gamma0EisensteinTotientSeries N s :=
  (gamma0EisensteinPositiveFirstDivisibilityEquiv N).tsum_eq
    (fun c : {c : ℕ // 0<c ∧ N∣c} => (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s))

end ArtinMatthews
