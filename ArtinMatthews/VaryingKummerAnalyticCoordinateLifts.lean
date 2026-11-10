module

public import ArtinMatthews.VaryingKummerAnalyticGaussianPacking
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! Passing from separation modulo the integer lattice to genuine separation
of all integer translates. Same-label translates are handled by their actual
nonzero integer coordinate. -/
namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
variable {β ι : Type*} [Fintype β]

def coordinateLift (x : ι → β → ℝ) (p : ι × (β → ℤ)) : β → ℝ := fun b =>
  x p.1 b + (p.2 b : ℝ)

theorem coordinate_integer_norm_one_le {k l : β → ℤ} (hkl : k ≠ l) :
    (1:ℝ) ≤ ‖(fun b => ((k b-l b : ℤ):ℝ))‖ := by
  obtain ⟨b,hb⟩ := Function.ne_iff.mp hkl
  have hi : (1:ℝ) ≤ |((k b-l b : ℤ):ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hb)
  exact hi.trans (norm_le_pi_norm (fun b => ((k b-l b : ℤ):ℝ)) b)

theorem coordinateLift_separated {Q : ℝ} (hQ : 1 ≤ Q) (x : ι → β → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖) :
    ∀ p q : ι × (β → ℤ), p ≠ q →
      1/Q ≤ ‖coordinateLift x p-coordinateLift x q‖ := by
  rintro ⟨i,k⟩ ⟨j,l⟩ hpq
  by_cases hij : i = j
  · subst j
    have hkl : k ≠ l := fun h => hpq (Prod.ext rfl h)
    have he : coordinateLift x (i,k)-coordinateLift x (i,l) =
        fun b => ((k b-l b : ℤ):ℝ) := by
      ext b
      simp only [coordinateLift,Pi.sub_apply,Int.cast_sub]
      ring
    rw [he]
    exact (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hQ |>.trans_eq (by norm_num)).trans
      (coordinate_integer_norm_one_le hkl)
  · have he : coordinateLift x (i,k)-coordinateLift x (j,l) =
        fun b => x i b-x j b+((k b-l b : ℤ):ℝ) := by
      ext b
      simp only [coordinateLift,Pi.sub_apply,Int.cast_sub]
      ring
    rw [he]
    exact hsep i j hij (k-l)

theorem coordinateLift_gaussian_summable {Q t : ℝ} (hQ : 1 ≤ Q) (ht : 0 < t)
    (x : ι → β → ℝ) (z : β → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖) :
    Summable (fun p : ι × (β → ℤ) =>
      Real.exp (-t*∑ b, (coordinateLift x p b-z b)^2)) :=
  coordinate_euclidean_gaussian_summable (by linarith) ht z (coordinateLift x)
    (coordinateLift_separated hQ x hsep)

theorem coordinateLift_gaussian_tsum_bound {Q t : ℝ} (hQ : 1 ≤ Q) (ht : 0 < t)
    (x : ι → β → ℝ) (z : β → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ k : β → ℤ,
      1/Q ≤ ‖(fun b => x i b-x j b+(k b:ℝ))‖) :
    (∑' p : ι × (β → ℤ), Real.exp (-t*∑ b, (coordinateLift x p b-z b)^2)) ≤
      coordinateGaussianConstant β*(1+Q/Real.sqrt t)^(Fintype.card β) :=
  coordinate_euclidean_gaussian_tsum_bound (by linarith) ht z (coordinateLift x)
    (coordinateLift_separated hQ x hsep)

end
end ArtinMatthews.VaryingKummerAnalytic
