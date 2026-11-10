module

public import ArtinMatthews.SpectralGamma0CuspPositiveHeightEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Scalar L2 restriction bounds at every positive cusp height, ready for
the actual energy-completion restriction maps. -/

namespace ArtinMatthews
noncomputable section

open Set MeasureTheory
open scoped MatrixGroups

theorem gamma0CuspSection_toLp_positive_height_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ C > 0, ∀ ψ : h2SmoothCompactSeeds,
      ‖(gamma0CuspSection_memLp_positive_height N ψ r Y hY).toLp (gamma0CuspSection N ψ r)‖ ≤
        C*‖gamma0EnergyTest N ψ‖ := by
  obtain ⟨C,hC,hbound⟩ := gamma0_cusp_positive_height_energy_bound N r Y hY
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun ψ => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hC.le, spectral_cusp_toLp_norm_square]
  apply le_trans _ (hbound ψ).2
  apply integral_mono
    ((gamma0CuspSection_memLp_positive_height N ψ r Y hY).integrable_norm_pow (by norm_num))
    (hbound ψ).1
  intro z
  exact le_add_of_nonneg_right (h2SectionEnergy_nonneg _ _)

end
end ArtinMatthews
