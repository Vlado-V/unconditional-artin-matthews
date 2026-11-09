module

public import ArtinMatthews.SpectralJPrincipalMass
public import ArtinMatthews.SpectralMixedCuspPrincipalCutoff


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped MatrixGroups
noncomputable section

theorem gamma0MixedCusp_nativePrincipal_summable
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (hsmall : Y < (1 / 16) / (|cuspFourierFrequency 1 n| /
      (gamma0CuspTrueWidth (r * s) (gamma0CuspOneOver s) : ℝ))) :
    Summable (fun i : Gamma0HeatPrincipalCuspidalIndex (r * s) =>
      gamma0NativePrincipalDensity (r * s) (gamma0CuspOneOver s) Y hY n hn i /
        (1 + |gamma0CuspPrincipalParameter (r * s) i.val|) ^ 4) := by
  obtain ⟨C, hC, hBound⟩ := gamma0MixedCusp_principal_cutoff_orbit_bessel
  let B := |cuspFourierFrequency 1 n|
  let D := C * (1 + B / ((r * s : ℕ) : ℝ))
  apply gamma0NativePrincipalDensity_summable_of_moment (r * s)
    (gamma0CuspOneOver s) Y hY n hn D (by dsimp only [D, B]; positivity)
  intro u R hR hprincipal hcap
  have h := hBound r s hcop u n hn hR hY hsmall hprincipal hcap
  apply h.trans
  have hq : 0 ≤ B / ((r * s : ℕ) : ℝ) := by dsimp only [B]; positivity
  have hR₂ : R ≤ R ^ 2 := by nlinarith only [hR]
  have hmul := mul_le_mul_of_nonneg_left hR₂ hq
  dsimp only [D, B]
  have hquad : R ^ 2 + B * R / ((r * s : ℕ) : ℝ) ≤
      (1 + B / ((r * s : ℕ) : ℝ)) * R ^ 2 := by
    rw [show B * R / ((r * s : ℕ) : ℝ) = (B / ((r * s : ℕ) : ℝ)) * R by ring]
    nlinarith only [hmul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hquad hC.le

end
end ArtinMatthews
