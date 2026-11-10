module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The actual old prime supplies the stretched-exponential saving used by
 the dirty-major row bound. This is the original logarithmic prime band. -/
namespace ArtinMatthews
noncomputable section

 theorem markedDirtyMajor_actual_prime_reciprocal {J : Type*} (e : J → ℝ)
    (he : ∀ j,(1/10:ℝ) ≤ e j) {x : ℝ} (hx : 1 ≤ Real.log x)
    (j : J) (particle : MarkedRawParticle (markedRawActualPrimeBand e x j)) :
    1/((particle.1.1:ℕ):ℝ) ≤ Real.exp (-((Real.log x)^(1/10:ℝ))) := by
  have hp : (particle.1.1:ℕ) ∈ markedLogPowerBand (e j) x :=
    (mem_markedRawPrimeBand _ _).mp particle.1.2
  calc
    _ ≤ 1/Real.exp ((Real.log x)^(e j)) :=
      one_div_le_one_div_of_le (Real.exp_pos _) (mem_markedLogPowerBand.mp hp).2.1
    _ = Real.exp (-((Real.log x)^(e j))) := by rw [one_div,Real.exp_neg]
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg
      (Real.rpow_le_rpow_of_exponent_le hx (he j)))

 theorem markedDirtyMajor_actual_band_count_bound {J : Type*} (e : J → ℝ)
    (he : ∀ j,(1/10:ℝ) ≤ e j) {x : ℝ} (hx : 1 ≤ Real.log x)
    (j : J) (particle : MarkedRawParticle (markedRawActualPrimeBand e x j))
    (T : Finset (ℤ × ℤ)) {C Y : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hcount : (T.card:ℝ) ≤ C*Y*(1/(particle.1.1:ℕ)+Y^(-1/10:ℝ))) :
    (T.card:ℝ) ≤ C*Y*(Real.exp (-((Real.log x)^(1/10:ℝ)))+Y^(-1/10:ℝ)) := by
  exact hcount.trans (mul_le_mul_of_nonneg_left
    (add_le_add (markedDirtyMajor_actual_prime_reciprocal e he hx j particle) le_rfl)
    (mul_nonneg hC hY))

end
end ArtinMatthews
