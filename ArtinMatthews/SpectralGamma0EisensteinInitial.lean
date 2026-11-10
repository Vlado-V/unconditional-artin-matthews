module

public import ArtinMatthews.SpectralGamma0EisensteinFourier
public import ArtinMatthews.SpectralGamma0EisensteinConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! Checked right-half-plane Eisenstein input; no continuous-spectrum resolution is assumed. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0Eisenstein_convergent_automorphic (N : ℕ) (s : ℂ) (hs : 1 < s.re) :
    (∀ z : UpperHalfPlane, Summable (fun v : Gamma0EisensteinRows N =>
      ‖gamma0EisensteinSummand N s v z‖)) ∧
    Continuous (gamma0Eisenstein N s) ∧
    ∀ (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
      gamma0Eisenstein N s ((g : SL(2,ℤ)) • z) = gamma0Eisenstein N s z :=
  ⟨gamma0EisensteinSummand_summable_norm N s hs,
    gamma0Eisenstein_continuous N s hs,gamma0Eisenstein_automorphy N s hs⟩

theorem gamma0Eisenstein_real_zero_coefficient_ne_zero (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) : gamma0EisensteinFourierCoefficient N (s : ℂ) y hy 0 ≠ 0 := by
  have hp := (Real.rpow_pos_of_pos hy s).trans_le
    (gamma0EisensteinFourier_zero_lower_bound N s hs y hy)
  intro he
  rw [he,Complex.zero_re] at hp
  exact lt_irrefl _ hp

end ArtinMatthews
