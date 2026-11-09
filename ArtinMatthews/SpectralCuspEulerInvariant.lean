module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
noncomputable section

def cuspEulerInvariant (c c' : ℝ → ℂ) (p q y : ℝ) : ℂ :=
  ((y^(-p):ℝ):ℂ)*((y:ℂ)*c' y-(q:ℂ)*c y)

/-- An actual first integral of the positive-half-line equation c''=c/y². -/
theorem cuspEulerInvariant_hasDerivAt_zero (c c' : ℝ → ℂ)
    (hc : ∀ y>0, HasDerivAt c (c' y) y)
    (hc' : ∀ y>0, HasDerivAt c' (c y/(y:ℂ)^2) y)
    {p q : ℝ} (hsum : p+q=1) (hprod : p*q = -1)
    {y : ℝ} (hy : 0 < y) : HasDerivAt (cuspEulerInvariant c c' p q) 0 y := by
  have hp := (Real.hasDerivAt_rpow_const (x := y) (p := -p) (Or.inl hy.ne')).ofReal_comp
  have hu := (((hasDerivAt_id y).ofReal_comp.mul (hc' y hy)).sub ((hc y hy).const_mul (q:ℂ)))
  have H := hp.mul hu
  have hpow : y^(-p-1) = y^(-p)/y := by rw [Real.rpow_sub hy,Real.rpow_one]
  have hsumc : (p:ℂ)+(q:ℂ)=1 := by exact_mod_cast hsum
  have hprodc : (p:ℂ)*(q:ℂ)= -1 := by exact_mod_cast hprod
  have hyc : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  convert H using 1
  · rfl
  · dsimp
    rw [hpow]
    push_cast
    field_simp
    linear_combination ((y^(-p):ℝ):ℂ)*(y:ℂ)*c' y*hsumc -
      ((y^(-p):ℝ):ℂ)*c y*hprodc

theorem cuspEulerInvariant_constant (c c' : ℝ → ℂ)
    (hc : ∀ y>0, HasDerivAt c (c' y) y)
    (hc' : ∀ y>0, HasDerivAt c' (c y/(y:ℂ)^2) y)
    {p q : ℝ} (hsum : p+q=1) (hprod : p*q = -1)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cuspEulerInvariant c c' p q x = cuspEulerInvariant c c' p q y := by
  have hd (z : ℝ) (hz : z ∈ Ioi (0:ℝ)) := cuspEulerInvariant_hasDerivAt_zero c c' hc hc' hsum hprod hz
  exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0:ℝ)).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hx hy

end
end ArtinMatthews
