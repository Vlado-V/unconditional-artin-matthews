module

public import ArtinMatthews.QuadraticHeckeMainTermEuler
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

private theorem nat_inverse_le_one (n : ℕ) : (n : ℝ)⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp only [hn, Nat.cast_zero, inv_zero, zero_le_one]
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)

theorem quadraticHeckeCoprimeDensity_ofReal (m : Ideal (𝓞 F)) :
    quadraticHeckeCoprimeDensity F m =
      ((∏ P ∈ HeckeIdealMobius.primeSupport F m,
        (1 - (Ideal.absNorm P : ℝ)⁻¹)) : ℝ) := by
  simp only [quadraticHeckeCoprimeDensity, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem quadraticHeckeCoprimeDensity_star (m : Ideal (𝓞 F)) :
    star (quadraticHeckeCoprimeDensity F m) = quadraticHeckeCoprimeDensity F m := by
  rw [quadraticHeckeCoprimeDensity_ofReal]
  exact Complex.conj_ofReal _

theorem quadraticHeckeCoprimeDensity_norm_le_one (m : Ideal (𝓞 F)) :
    ‖quadraticHeckeCoprimeDensity F m‖ ≤ 1 := by
  rw [quadraticHeckeCoprimeDensity_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg (fun P _ => sub_nonneg.mpr (nat_inverse_le_one _)))]
  apply Finset.prod_le_one₀
  · intro P _
    exact sub_nonneg.mpr (nat_inverse_le_one _)
  · intro P _
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem quadraticHeckeCoprimeDensity_mul_norm_le (m : Ideal (𝓞 F)) (z : ℂ) :
    ‖quadraticHeckeCoprimeDensity F m * z‖ ≤ ‖z‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (quadraticHeckeCoprimeDensity_norm_le_one F m)
    (norm_nonneg z)).trans_eq (one_mul _)

theorem quadraticHeckeCoprimeDensity_mass_le {ι : Type*} (s : Finset ι)
    (m : ι → Ideal (𝓞 F)) (u : ι → ℂ) :
    (∑ i ∈ s, ‖quadraticHeckeCoprimeDensity F (m i) * u i‖ ^ 2) ≤
      ∑ i ∈ s, ‖u i‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (quadraticHeckeCoprimeDensity_mul_norm_le F (m i) (u i)) 2

end
end ArtinMatthews
