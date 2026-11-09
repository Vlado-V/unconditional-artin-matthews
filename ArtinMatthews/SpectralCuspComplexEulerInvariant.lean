module

public import ArtinMatthews.SpectralEisensteinVerticalCutoff
public import Mathlib.Analysis.Calculus.MeanValue


set_option backward.privateInPublic true
@[expose] public section

/-! Complex Euler first integrals on a positive-height cusp ray. -/
namespace ArtinMatthews
noncomputable section
open Set

def cuspComplexEulerInvariant (c g : ℝ → ℂ) (p q : ℂ) (y : ℝ) : ℂ :=
  (y:ℂ)^(-p)*((y:ℂ)*g y-q*c y)

theorem cuspComplexEulerInvariant_hasDerivAt_zero (c g : ℝ → ℂ) {Y : ℝ}
    (hY : 0≤Y) (eig p q : ℂ) (hpq : p+q=1) (hprod : p*q=eig)
    (hc : ∀ y>Y, HasDerivAt c (g y) y)
    (hg : ∀ y>Y, HasDerivAt g (-eig*c y/(y:ℂ)^2) y)
    {y : ℝ} (hy : Y<y) : HasDerivAt (cuspComplexEulerInvariant c g p q) 0 y := by
  have hy0 := lt_of_le_of_lt hY hy
  have hpow := eisensteinPositivePower_hasDerivAt (-p) y hy0
  have hu := (((hasDerivAt_id y).ofReal_comp.mul (hg y hy)).sub ((hc y hy).const_mul q))
  have H := hpow.mul hu
  have hn : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hy0.ne'
  convert H using 1
  · rfl
  · dsimp
    rw [Complex.cpow_sub (-p) 1 hn,Complex.cpow_one]
    field_simp
    linear_combination (y:ℂ)^(-p)*(y:ℂ)*g y*hpq-
      (y:ℂ)^(-p)*c y*hprod

theorem cuspComplexEulerInvariant_constant (c g : ℝ → ℂ) {Y : ℝ}
    (hY : 0≤Y) (eig p q : ℂ) (hpq : p+q=1) (hprod : p*q=eig)
    (hc : ∀ y>Y, HasDerivAt c (g y) y)
    (hg : ∀ y>Y, HasDerivAt g (-eig*c y/(y:ℂ)^2) y)
    {x y : ℝ} (hx : Y<x) (hy : Y<y) :
    cuspComplexEulerInvariant c g p q x=cuspComplexEulerInvariant c g p q y := by
  have hd (z : ℝ) (hz : z ∈ Ioi Y) :=
    cuspComplexEulerInvariant_hasDerivAt_zero c g hY eig p q hpq hprod hc hg hz
  exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi Y).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hx hy

end
end ArtinMatthews
