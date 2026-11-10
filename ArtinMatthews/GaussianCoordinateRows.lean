module

public import ArtinMatthews.GaussianCoordinateEnergy
public import ArtinMatthews.VaryingKummerAnalyticGaussianPacking
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Finset VaryingKummerAnalytic
noncomputable section
variable {β ι : Type*} [Fintype β]

def coordinateGaussianLift (x : ι → β → ℝ) (p : ι × (β → ℤ)) : β → ℝ :=
  fun b => x p.1 b+(p.2 b:ℝ)

/-- The actual periodized Gaussian row over finitely many frequencies is
controlled by packing all their integer translates. -/
theorem coordinatePeriodizedGaussian_row_bound {Q t : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ u v : {i // i ∈ P} × (β → ℤ), u ≠ v →
      1/Q ≤ ‖coordinateGaussianLift x (u.1.val,u.2)-coordinateGaussianLift x (v.1.val,v.2)‖)
    (z : β → ℝ) :
    (∑ i ∈ P, coordinatePeriodizedGaussian t (z-x i)) ≤
      coordinateGaussianConstant β*(1+Q/Real.sqrt t)^(Fintype.card β) := by
  classical
  let lift := fun u : {i // i ∈ P} × (β → ℤ) => coordinateGaussianLift x (u.1.val,u.2)
  let f := fun u : {i // i ∈ P} × (β → ℤ) => Real.exp (-t*∑ b, (lift u b-z b)^2)
  have hf : Summable f := coordinate_euclidean_gaussian_summable hQ ht z lift hsep
  have hb := coordinate_euclidean_gaussian_tsum_bound hQ ht z lift hsep
  have he (i : {i // i ∈ P}) (m : β → ℤ) : f (i,m) =
      Real.exp (-t*∑ b, ((m b:ℝ)-(z-x i.val) b)^2) := by
    dsimp [f,lift,coordinateGaussianLift]
    congr 1
    congr 1
    apply sum_congr rfl
    intro b _
    ring
  have htotal : (∑' u, f u) = ∑ i ∈ P, coordinatePeriodizedGaussian t (z-x i) := by
    rw [hf.tsum_prod]
    simp_rw [he]
    rw [tsum_fintype]
    exact sum_coe_sort P (fun i => coordinatePeriodizedGaussian t (z-x i))
  rw [htotal] at hb
  exact hb

theorem coordinateGaussianKernel_row_bound {Q a : ℝ} (hQ : 0 < Q) (ha : 0 < a)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ u v : {i // i ∈ P} × (β → ℤ), u ≠ v →
      1/Q ≤ ‖coordinateGaussianLift x (u.1.val,u.2)-coordinateGaussianLift x (v.1.val,v.2)‖)
    (z : β → ℝ) :
    (∑ i ∈ P, ‖coordinateGaussianKernel a (z-x i)‖) ≤
      (1/Real.sqrt a)^(Fintype.card β)*
        (coordinateGaussianConstant β*(1+Q/Real.sqrt (Real.pi/a))^(Fintype.card β)) := by
  simp_rw [coordinateGaussianKernel_norm ha]
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left
    (coordinatePeriodizedGaussian_row_bound hQ (div_pos Real.pi_pos ha) P x hsep z) (by positivity)

/-- Genuine Gaussian energy bound in arbitrary finite dimension, with all
kernel rows discharged by separation of the actual lifted frequency family. -/
theorem coordinateGaussianEnergy_bound {Q a : ℝ} (hQ : 0 < Q) (ha : 0 < a)
    (P : Finset ι) (x : ι → β → ℝ)
    (hsep : ∀ u v : {i // i ∈ P} × (β → ℤ), u ≠ v →
      1/Q ≤ ‖coordinateGaussianLift x (u.1.val,u.2)-coordinateGaussianLift x (v.1.val,v.2)‖)
    (v : ι → ℂ) :
    (∑' n : β → ℤ, coordinateGaussianWeight a n*‖coordinateDualPolynomial P x v n‖^2) ≤
      ((1/Real.sqrt a)^(Fintype.card β)*
        (coordinateGaussianConstant β*(1+Q/Real.sqrt (Real.pi/a))^(Fintype.card β)))*
          ∑ p ∈ P, ‖v p‖^2 := by
  apply coordinateGaussianEnergy_schur ha P x (fun i j => ‖coordinateGaussianKernel a (x i-x j)‖)
  · exact fun _ _ _ _ => norm_nonneg _
  · exact fun _ _ _ _ => coordinateGaussianKernel_norm_sub_symm _ _ _
  · exact fun _ _ _ _ => le_rfl
  · exact fun i _ => coordinateGaussianKernel_row_bound hQ ha P x hsep (x i)

end
end ArtinMatthews
