module

public import ArtinMatthews.SpectralCuspEulerInvariant
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem cuspEuler_firstOrder_identity (c c' : ℝ → ℂ)
    (hc : ∀ y>0, HasDerivAt c (c' y) y)
    (hc' : ∀ y>0, HasDerivAt c' (c y/(y:ℂ)^2) y)
    {p q : ℝ} (hsum : p+q=1) (hprod : p*q = -1)
    {y : ℝ} (hy : 0 < y) :
    (y:ℂ)*c' y-(q:ℂ)*c y = ((y^p:ℝ):ℂ)*(c' 1-(q:ℂ)*c 1) := by
  have H := cuspEulerInvariant_constant c c' hc hc' hsum hprod hy (by norm_num : (0:ℝ)<1)
  simp only [cuspEulerInvariant,Real.one_rpow,Complex.ofReal_one,one_mul] at H
  have he : ((y^p:ℝ):ℂ)*((y^(-p):ℝ):ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.rpow_add hy,add_neg_cancel,Real.rpow_zero,Complex.ofReal_one]
  calc
    _ = (((y^p:ℝ):ℂ)*((y^(-p):ℝ):ℂ))*((y:ℂ)*c' y-(q:ℂ)*c y) := by rw [he,one_mul]
    _ = _ := by rw [mul_assoc,H]

theorem cuspEuler_solution_formula (c c' : ℝ → ℂ)
    (hc : ∀ y>0, HasDerivAt c (c' y) y)
    (hc' : ∀ y>0, HasDerivAt c' (c y/(y:ℂ)^2) y)
    {p q : ℝ} (hsum : p+q=1) (hprod : p*q = -1) (hpq : p ≠ q)
    {y : ℝ} (hy : 0 < y) :
    c y = (((y^p:ℝ):ℂ)*(c' 1-(q:ℂ)*c 1)-((y^q:ℝ):ℂ)*(c' 1-(p:ℂ)*c 1))/((p:ℂ)-(q:ℂ)) := by
  have hp := cuspEuler_firstOrder_identity c c' hc hc' hsum hprod hy
  have hq := cuspEuler_firstOrder_identity c c' hc hc' (by linarith : q+p=1)
    (by simpa only [mul_comm] using hprod) hy
  have hd : (p:ℂ)-(q:ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hpq
  apply (eq_div_iff hd).mpr
  calc
    _ = ((y:ℂ)*c' y-(q:ℂ)*c y)-((y:ℂ)*c' y-(p:ℂ)*c y) := by ring
    _ = _ := by rw [hp,hq]

def cuspEulerPlus : ℝ := (1+Real.sqrt 5)/2
def cuspEulerMinus : ℝ := (1-Real.sqrt 5)/2

theorem cuspEuler_roots : cuspEulerPlus+cuspEulerMinus=1 ∧
    cuspEulerPlus*cuspEulerMinus = -1 ∧ cuspEulerPlus ≠ cuspEulerMinus := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<5)
  dsimp [cuspEulerPlus,cuspEulerMinus]
  constructor
  · ring
  constructor
  · nlinarith
  · intro h
    linarith

/-- Every genuine classical solution of c''=c/y² on y>0 is the linear
combination of the two Euler powers, with no spectral or ODE premise added. -/
theorem cuspEuler_solution_classification (c c' : ℝ → ℂ)
    (hc : ∀ y>0, HasDerivAt c (c' y) y)
    (hc' : ∀ y>0, HasDerivAt c' (c y/(y:ℂ)^2) y) :
    ∃ A B : ℂ, ∀ y>0,
      c y = A*((y^cuspEulerPlus:ℝ):ℂ)+B*((y^cuspEulerMinus:ℝ):ℂ) := by
  let d : ℂ := (cuspEulerPlus:ℂ)-(cuspEulerMinus:ℂ)
  refine ⟨(c' 1-(cuspEulerMinus:ℂ)*c 1)/d,
    ((cuspEulerPlus:ℂ)*c 1-c' 1)/d,?_⟩
  intro y hy
  rw [cuspEuler_solution_formula c c' hc hc' cuspEuler_roots.1 cuspEuler_roots.2.1 cuspEuler_roots.2.2 hy]
  dsimp [d]
  ring

end
end ArtinMatthews
