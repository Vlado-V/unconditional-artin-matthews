module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ArtinMatthews.SourceQuadraticDualLosses
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

namespace ArtinMatthews
noncomputable section

theorem quadraticDual_small_total_power_loss {M P K A η θ ε : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hA : 0 ≤ A) (hAK : A ≤ K) (hKM : K ≤ M)
    (hη : 0 ≤ η) (hsum : 3*η+θ ≤ ε) :
    ((A*P)^η * (2*P)^η) * (M*P)^θ ≤ (2:ℝ)^(2*η) * (M*P)^ε := by
  have hK : 0 ≤ K := hA.trans hAK
  have hMP : 1 ≤ M*P := one_le_mul_of_one_le_of_one_le hM hP
  have hOne : 1 ≤ (M*P)^η := Real.one_le_rpow hMP hη
  calc
    _ ≤ ((2*K*P)^η * (2*P)^η) * (M*P)^θ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact Real.rpow_le_rpow (by positivity) (by nlinarith) hη
    _ ≤ (((2*K*P)^η * (2*P)^η) * (M*P)^η) * (M*P)^θ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hOne) (by positivity)
    _ ≤ _ := quadraticDual_total_power_loss hM hP hK hKM hη hsum

theorem quadraticDual_weighted_total_power_loss {M P K η θ ε C L : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hK : 0 ≤ K) (hKM : K ≤ M)
    (hη : 0 ≤ η) (hsum : 3*η+θ ≤ ε) (hC : 0 ≤ C) (hL : L ≤ C*(M*P)^η) :
    ((2*K*P)^η * (2*P)^η) * L * (M*P)^θ ≤ C * (2:ℝ)^(2*η) * (M*P)^ε := by
  calc
    _ ≤ ((2*K*P)^η * (2*P)^η) * (C*(M*P)^η) * (M*P)^θ := by gcongr
    _ = C * (((2*K*P)^η * (2*P)^η) * (M*P)^η * (M*P)^θ) := by ring
    _ ≤ C * ((2:ℝ)^(2*η) * (M*P)^ε) :=
      mul_le_mul_of_nonneg_left (quadraticDual_total_power_loss hM hP hK hKM hη hsum) hC
    _ = _ := by ring

end
end ArtinMatthews
