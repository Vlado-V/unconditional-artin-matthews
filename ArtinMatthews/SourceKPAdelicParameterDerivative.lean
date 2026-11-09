module

public import ArtinMatthews.SourceKPAdelicParameterBounds
public import Mathlib.Analysis.Calculus.Deriv.Slope


set_option backward.privateInPublic true
@[expose] public section

/-! Spectral derivatives of the actual flat section, with an integrable
two-endpoint bound on every smaller vertical strip. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCompactScalar_hasDerivAt (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K])
    (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    HasDerivAt (fun z : ℂ => sourceKPAdelicCompactScalar K hζ z q)
      ((Real.log (sourceKPAdelicHeight K hζ g) : ℂ) *
        sourceKPAdelicCompactScalar K hζ s q) s := by
  let l : ℂ := Real.log (sourceKPAdelicHeight K hζ g)
  have hd := (((hasDerivAt_id s).mul_const l).cexp).mul_const
    (sourceKPAdelicCompactScalar K hζ 0 q)
  convert hd using 1
  · funext z
    exact sourceKPAdelicCompactScalar_flat K hζ z q g hp
  · rw [sourceKPAdelicCompactScalar_flat K hζ s q g hp]
    dsimp [l]
    ring

private theorem sourceKPExpSlope_bound (a b r l δ : ℝ)
    (hr : a + δ ≤ r ∧ r ≤ b - δ) :
    δ * (|l| * Real.exp (r*l)) ≤ Real.exp (a*l) + Real.exp (b*l) := by
  by_cases hl : 0 ≤ l
  · rw [abs_of_nonneg hl]
    have ht : δ*l ≤ Real.exp (δ*l) := by
      linarith [Real.add_one_le_exp (δ*l)]
    calc
      δ * (l * Real.exp (r*l)) = (δ*l) * Real.exp (r*l) := by ring
      _ ≤ Real.exp (δ*l) * Real.exp (r*l) :=
        mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
      _ = Real.exp ((r+δ)*l) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (b*l) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith [hr.2]) hl)
      _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le
  · have hl' : l ≤ 0 := le_of_not_ge hl
    rw [abs_of_nonpos hl']
    have ht : δ*(-l) ≤ Real.exp (δ*(-l)) := by
      linarith [Real.add_one_le_exp (δ*(-l))]
    calc
      δ * (-l * Real.exp (r*l)) = (δ*(-l)) * Real.exp (r*l) := by ring
      _ ≤ Real.exp (δ*(-l)) * Real.exp (r*l) :=
        mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
      _ = Real.exp ((r-δ)*l) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (a*l) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right (by linarith [hr.1]) hl')
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le

theorem sourceKPAdelicCompactScalar_deriv_bound (a b δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs : a + δ ≤ s.re ∧ s.re ≤ b - δ)
    (q : SourceKPAdelicProjective K hζ) :
    ‖deriv (fun z : ℂ => sourceKPAdelicCompactScalar K hζ z q) s‖ ≤
      δ⁻¹ * (‖sourceKPAdelicCompactScalar K hζ (a : ℂ) q‖ +
        ‖sourceKPAdelicCompactScalar K hζ (b : ℂ) q‖) := by
  obtain ⟨g,hg⟩ := ProjGenLinGroup.mk_surjective (sourceKPAdelicProjectiveProjection K hζ q)
  rw [(sourceKPAdelicCompactScalar_hasDerivAt K hζ s q g hg.symm).deriv,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    sourceKPAdelicCompactScalar_norm_flat K hζ s q g hg.symm,
    sourceKPAdelicCompactScalar_norm_flat K hζ (a : ℂ) q g hg.symm,
    sourceKPAdelicCompactScalar_norm_flat K hζ (b : ℂ) q g hg.symm]
  simp only [Complex.ofReal_re]
  have hb := mul_le_mul_of_nonneg_right
    (sourceKPExpSlope_bound a b s.re (Real.log (sourceKPAdelicHeight K hζ g)) δ hs)
    (norm_nonneg (sourceKPAdelicCompactScalar K hζ 0 q))
  apply (le_inv_mul_iff₀ hδ).mpr
  nlinarith only [hb]

theorem sourceKPAdelicIntertwiningKernel_deriv_bound (a b δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs : a + δ ≤ s.re ∧ s.re ≤ b - δ)
    (g : SourceKPAdelicProjective K hζ) (y : 𝔸[K]) :
    ‖deriv (fun z : ℂ => sourceKPAdelicIntertwiningKernel K hζ z g y) s‖ ≤
      δ⁻¹ * (‖sourceKPAdelicIntertwiningKernel K hζ (a : ℂ) g y‖ +
        ‖sourceKPAdelicIntertwiningKernel K hζ (b : ℂ) g y‖) :=
  sourceKPAdelicCompactScalar_deriv_bound K hζ a b δ hδ s hs _

end
end ArtinMatthews
