module

public import ArtinMatthews.SpectralGamma0EisensteinRows
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized Γ₀(N) Eisenstein sum in its convergent half-plane. -/
noncomputable section
open Set Filter
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0EisensteinSummand (N : ℕ) (s : ℂ) (v : Gamma0EisensteinRows N)
    (z : UpperHalfPlane) : ℂ := (gamma0EisensteinHeight N v z : ℂ)^s

theorem gamma0EisensteinSummand_norm (N : ℕ) (s : ℂ) (v : Gamma0EisensteinRows N)
    (z : UpperHalfPlane) :
    ‖gamma0EisensteinSummand N s v z‖ = (gamma0EisensteinHeight N v z)^s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (gamma0EisensteinHeight_pos N v z) s

theorem gamma0EisensteinSummand_norm_row (N : ℕ) (s : ℂ) (v : Gamma0EisensteinRows N)
    (z : UpperHalfPlane) :
    ‖gamma0EisensteinSummand N s v z‖ =
      z.im^s.re * ‖(v.val 0 : ℂ)*z+v.val 1‖^(-(2*s.re)) := by
  rw [gamma0EisensteinSummand_norm,gamma0EisensteinHeight_row,
    Real.div_rpow z.im_pos.le (sq_nonneg _),
    ← Real.rpow_natCast_mul (norm_nonneg _) 2 s.re]
  rw [div_eq_mul_inv,Real.rpow_neg (norm_nonneg _)]
  norm_num

theorem gamma0EisensteinSummand_norm_bound (N : ℕ) (s : ℂ) (hs : 0 ≤ s.re)
    (v : Gamma0EisensteinRows N) (z : UpperHalfPlane) :
    ‖gamma0EisensteinSummand N s v z‖ ≤
      (z.im^s.re * (EisensteinSeries.r z)^(-(2*s.re))) * ‖v.val‖^(-(2*s.re)) := by
  rw [gamma0EisensteinSummand_norm_row]
  have h := EisensteinSeries.summand_bound z (show 0 ≤ 2*s.re by positivity) v.val
  exact (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg z.im_pos.le s.re)).trans_eq (mul_assoc _ _ _).symm

theorem gamma0EisensteinSummand_summable_norm (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) : Summable (fun v : Gamma0EisensteinRows N => ‖gamma0EisensteinSummand N s v z‖) := by
  have h := (EisensteinSeries.summable_one_div_norm_rpow (show 2 < 2*s.re by linarith)).subtype
    (fun v => v ∈ Set.range (gamma0EisensteinRow N))
  exact (h.mul_left (z.im^s.re * (EisensteinSeries.r z)^(-(2*s.re)))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => gamma0EisensteinSummand_norm_bound N s (by linarith) v z)

theorem gamma0EisensteinSummand_summable (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (z : UpperHalfPlane) : Summable (fun v : Gamma0EisensteinRows N => gamma0EisensteinSummand N s v z) :=
  (gamma0EisensteinSummand_summable_norm N s hs z).of_norm

def gamma0Eisenstein (N : ℕ) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  (1/2 : ℂ) * ∑' v : Gamma0EisensteinRows N, gamma0EisensteinSummand N s v z

theorem gamma0Eisenstein_hasSum (N : ℕ) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    HasSum (fun v : Gamma0EisensteinRows N => (1/2 : ℂ)*gamma0EisensteinSummand N s v z)
      (gamma0Eisenstein N s z) :=
  (gamma0EisensteinSummand_summable N s hs z).hasSum.mul_left (1/2 : ℂ)

theorem gamma0EisensteinSummand_automorphy (N : ℕ) (s : ℂ)
    (v : Gamma0EisensteinRows N) (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0EisensteinSummand N s v ((g : SL(2,ℤ)) • z) =
      gamma0EisensteinSummand N s (gamma0EisensteinRowEquiv N g v) z := by
  unfold gamma0EisensteinSummand
  rw [gamma0EisensteinHeight_right]

theorem gamma0Eisenstein_automorphy (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    gamma0Eisenstein N s ((g : SL(2,ℤ)) • z) = gamma0Eisenstein N s z := by
  have h := (gamma0EisensteinRowEquiv N g).hasSum_iff.mpr
    (gamma0Eisenstein_hasSum N s hs z)
  exact (gamma0Eisenstein_hasSum N s hs ((g : SL(2,ℤ)) • z)).unique
    (h.congr_fun (fun v => by simp only [Function.comp_apply,gamma0EisensteinSummand_automorphy]))

theorem gamma0EisensteinSummand_differentiable_s (N : ℕ) (v : Gamma0EisensteinRows N)
    (z : UpperHalfPlane) : Differentiable ℂ (fun s => gamma0EisensteinSummand N s v z) := by
  exact differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr (gamma0EisensteinHeight_pos N v z).ne'))

end ArtinMatthews
