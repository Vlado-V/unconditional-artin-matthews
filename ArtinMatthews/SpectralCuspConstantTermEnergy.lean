module

public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralCuspVerticalEnergy
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

/-! Actual weighted tail and near-zero energy of the globally glued constant
term, obtained from its genuine all-height Hilbert restrictions. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0GlobalCuspConstantTerm_energy_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (Y : ℝ) (hY : 0 < Y) :
    (fun y : ℝ => ‖gamma0GlobalCuspConstantTerm N r f y‖ ^ 2 / y ^ 2)
      =ᵐ[volume.restrict (Ioi Y)]
        fun y : ℝ => ‖gamma0CuspConstantTerm N r Y hY f y‖ ^ 2 / y ^ 2 := by
  have he := (spectralCuspVerticalL2_ae_iff
    (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
      (gamma0GlobalCuspConstantTerm_ae N r f Y hY)
  exact he.mono fun y hy => by
    dsimp only
    rw [hy]

theorem gamma0GlobalCuspConstantTerm_integrable_energy (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (Y : ℝ) (hY : 0 < Y) :
    IntegrableOn (fun y : ℝ => ‖gamma0GlobalCuspConstantTerm N r f y‖ ^ 2 / y ^ 2)
      (Ioi Y) volume :=
  (cuspVerticalL2_integrable_energy (Nat.cast_pos.mpr (NeZero.pos N)) hY
    (gamma0CuspConstantTerm N r Y hY f)).congr
      (gamma0GlobalCuspConstantTerm_energy_ae N r f Y hY).symm

theorem gamma0GlobalCuspConstantTerm_energy_eq (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (Y : ℝ) (hY : 0 < Y) :
    (∫ y in Ioi Y, ‖gamma0GlobalCuspConstantTerm N r f y‖ ^ 2 / y ^ 2) =
      ‖gamma0CuspConstantTerm N r Y hY f‖ ^ 2 / (N : ℝ) := by
  rw [integral_congr_ae (gamma0GlobalCuspConstantTerm_energy_ae N r f Y hY)]
  exact cuspVerticalL2_energy_eq (Nat.cast_pos.mpr (NeZero.pos N)) hY _

theorem gamma0GlobalCuspConstantTerm_near_zero_energy (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (Y : ℝ) (hY : 0 < Y) (hY1 : Y ≤ 1) :
    (∫ y in Icc Y 1, ‖gamma0GlobalCuspConstantTerm N r f y‖ ^ 2 / y ^ 2) ≤
      (25 * ((N : ℝ) + 1) * ‖f‖ ^ 2 / (N : ℝ)) / Y ^ 2 := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hsub : (∫ y in Icc Y 1, ‖gamma0GlobalCuspConstantTerm N r f y‖ ^ 2 / y ^ 2) ≤
      ∫ y in Ioi Y, ‖gamma0GlobalCuspConstantTerm N r f y‖ ^ 2 / y ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc]
    apply setIntegral_mono_set (gamma0GlobalCuspConstantTerm_integrable_energy N r f Y hY)
    · exact Eventually.of_forall fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact Eventually.of_forall fun _ hy => hy.1
  calc
    _ ≤ (∫ y in Ioi Y, ‖gamma0GlobalCuspConstantTerm N r f y‖ ^ 2 / y ^ 2) := hsub
    _ = ‖gamma0CuspConstantTerm N r Y hY f‖ ^ 2 / (N : ℝ) :=
      gamma0GlobalCuspConstantTerm_energy_eq N r f Y hY
    _ ≤ ((25 * ((N : ℝ) + 1) / Y ^ 2) * ‖f‖ ^ 2) / (N : ℝ) :=
      div_le_div_of_nonneg_right
        (gamma0CuspConstantTerm_norm_sq_quadratic N r Y hY hY1 f) hN.le
    _ = _ := by ring

end ArtinMatthews
