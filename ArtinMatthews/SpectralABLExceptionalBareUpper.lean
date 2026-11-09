module

public import ArtinMatthews.SpectralABLSourceBareTrace
public import ArtinMatthews.SpectralABLExceptionalKLMass


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exceptional bare diagonal and its fixed-parameter Weil scale. -/

noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0ABLExceptional_bare_diagonal_norm_le (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (a : ℝ) (A : ℕ) (hA : 3 ≤ A) (B : ℝ)
    (hB : ‖∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r r c n n
      (spectralABLExceptionalCorrected a A)‖ ≤ B) :
    ‖gamma0BareSourceSpectralSide N (spectralABLExceptionalEnergyTest a A (by omega))
      r r Y hY n n hn hn‖ ≤ (spectralABLExceptionalBound A/Real.pi+B)/4 := by
  rw [gamma0ABLExceptional_sameCusp_bare_source_trace N r Y hY n n hn hn a A hA,
    if_pos rfl, norm_mul]
  have hquarter : ‖(1/4 : ℂ)‖ = (1/4 : ℝ) := by
    rw [norm_div, norm_one, show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
      Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  rw [hquarter]
  calc
    _ ≤ (1/4 : ℝ)*(‖spectralABLBareDiagonal (spectralABLExceptionalCorrected a A)‖+
        ‖∑' c : Ioi (0 : ℕ), gamma0TrueWidthBareFibre N r r c n n
          (spectralABLExceptionalCorrected a A)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1/4 : ℝ)*(spectralABLExceptionalBound A/Real.pi+B) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (spectralABLExceptionalBareDiagonal_norm_le a hA) hB) (by norm_num)
    _ = _ := by ring

theorem spectralABLExceptional_weil_factor_eq (N : ℕ) (n : ℤ) (ε a : ℝ)
    (ha : 0 < a) :
    ((N : ℝ)*(n.natAbs : ℝ)/a)^ε*
      (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/((N : ℝ)*a)) =
      (((N : ℝ)*(n.natAbs : ℝ))^ε*
        (Real.sqrt ((n.natAbs : ℝ)*(Nat.gcd N n.natAbs : ℝ))/(N : ℝ)))*a^(-1-ε) := by
  rw [Real.div_rpow (by positivity) ha.le, show -1-ε = -1+(-ε) by ring,
    Real.rpow_add ha, Real.rpow_neg_one, Real.rpow_neg ha.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ArtinMatthews
