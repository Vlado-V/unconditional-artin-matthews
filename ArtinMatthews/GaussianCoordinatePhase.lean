module

public import ArtinMatthews.GaussianCoordinateOneDim
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section
open Finset
variable {β : Type*} [Fintype β]

def coordinatePhase (ξ : β → ℝ) (n : β → ℤ) : ℂ :=
  Complex.exp (((2*Real.pi*(∑ i, ξ i*(n i:ℝ)):ℝ):ℂ)*Complex.I)

def coordinateGaussianWeight (a : ℝ) (n : β → ℤ) : ℝ :=
  Real.exp (-Real.pi*a*(∑ i, (n i:ℝ)^2))

theorem coordinatePhase_norm (ξ : β → ℝ) (n : β → ℤ) : ‖coordinatePhase ξ n‖ = 1 := by
  rw [coordinatePhase,Complex.norm_exp]
  simp

theorem coordinatePhase_sub (ξ η : β → ℝ) (n : β → ℤ) :
    coordinatePhase (ξ-η) n = coordinatePhase ξ n*star (coordinatePhase η n) := by
  unfold coordinatePhase
  simp only [← starRingEnd_apply]
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [Pi.sub_apply,sub_mul,sum_sub_distrib]
  push_cast
  simp only [map_sum,map_mul,map_intCast,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem coordinatePhase_zero (n : β → ℤ) : coordinatePhase (0 : β → ℝ) n = 1 := by
  simp [coordinatePhase]

theorem coordinatePhase_neg (ξ : β → ℝ) (n : β → ℤ) :
    coordinatePhase (-ξ) n = star (coordinatePhase ξ n) := by
  simpa only [zero_sub,coordinatePhase_zero,one_mul] using coordinatePhase_sub (0 : β → ℝ) ξ n

theorem coordinateGaussianWeight_nonneg (a : ℝ) (n : β → ℤ) :
    0 ≤ coordinateGaussianWeight a n := (Real.exp_pos _).le

theorem coordinateGaussianWeight_phase (a : ℝ) (ξ : β → ℝ) (n : β → ℤ) :
    (coordinateGaussianWeight a n:ℂ)*coordinatePhase ξ n =
      ∏ i, coordinateGaussianFactor a (ξ i) (n i) := by
  unfold coordinateGaussianWeight coordinatePhase coordinateGaussianFactor
  rw [prod_mul_distrib,← Complex.exp_sum,← Complex.exp_sum,Complex.ofReal_exp]
  congr 1
  · push_cast
    simp only [mul_sum]
  · push_cast
    simp only [mul_sum,sum_mul,mul_assoc]

end
end ArtinMatthews
