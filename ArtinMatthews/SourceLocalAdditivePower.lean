module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.ProbeIdealSourceRegions
public import ArtinMatthews.SourceKPCoupledTameAbsolute
public import ArtinMatthews.SourceKPCoupledTameShellMeasure
public import ArtinMatthews.StandardLocalBallDilation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Integrability of the finite-place height power against actual additive Haar. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain MeasureTheory SourcePhysical
open scoped NumberField BigOperators Topology

noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "Q" => (Ideal.absNorm P.asIdeal : ℝ)
local notation "μ₀" => sourceJacquetHaar K P

theorem sourceKPLocalAdditivePower_integrable {a : ℝ} (ha : 1 < a) :
    Integrable (fun x : L => (max 1 ‖x‖) ^ (-a)) μ₀ := by
  let f : L → ℝ := fun x => (max 1 ‖x‖) ^ (-a)
  let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P
  have hQ : 1 < Q := VaryingKummerAnalytic.probeIdealPrime_norm_gt_one K P
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hc : Continuous f := by
    apply (continuous_const.max continuous_norm).rpow_const
    intro x
    exact Or.inl (zero_lt_one.trans_le (le_max_left (1 : ℝ) ‖x‖)).ne'
  have hq : Real.exp ((1 - a) * Real.log Q) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr ha) (Real.log_pos hQ)
  have hterm (l : ℕ) (x : L) (hx : x ∈ sourceJacquetValuationShell K P (l : ℤ)) :
      ‖f x‖ = Real.exp (-a * (l : ℝ) * Real.log Q) := by
    have hv := (sourceJacquetValuationShell_mem K P (l : ℤ) x).mp hx
    have hx0 : x ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    have hn : ‖x‖ = Q ^ l := by
      rw [sourceLocalNorm_eq_zpow K P x hx0, hv, WithZero.log_exp, zpow_natCast]
    dsimp only [f]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _), hn,
      max_eq_right (one_le_pow₀ hQ.le), ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le,
      Real.rpow_def_of_pos hQ0]
    congr 1
    ring
  have hvol (l : ℕ) : (μ₀).real (sourceJacquetValuationShell K P (l : ℤ)) ≤ Q ^ l := by
    rw [sourceKPCoupledJacquetShell_mass K P]
    exact mul_le_of_le_one_right (pow_nonneg hQ0.le _) (sub_le_self _ (inv_nonneg.mpr hQ0.le))
  have hbound (l : ℕ) :
      (∫ x in sourceJacquetValuationShell K P (l : ℤ), ‖f x‖ ∂μ₀) ≤
        (Real.exp ((1 - a) * Real.log Q)) ^ l := by
    calc
      _ = ∫ _x in sourceJacquetValuationShell K P (l : ℤ),
          Real.exp (-a * (l : ℝ) * Real.log Q) ∂μ₀ := by
        apply setIntegral_congr_fun (sourceJacquetValuationShell_isCompact K P (l : ℤ)).measurableSet
        exact hterm l
      _ ≤ Q ^ l * Real.exp (-a * (l : ℝ) * Real.log Q) := by
        rw [setIntegral_const, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hvol l) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hQ0, ← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
  have hsummable : Summable (fun l : ℕ =>
      ∫ x in sourceJacquetValuationShell K P (l : ℤ), ‖f x‖ ∂μ₀) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound
      (summable_geometric_of_lt_one (Real.exp_pos _).le hq)
  have hball := hc.continuousOn.integrableOn_compact (μ := μ₀) (sourceLocalBall_isCompact K P 0)
  have hshell : IntegrableOn f (⋃ l : ℕ, sourceJacquetValuationShell K P (l : ℤ)) μ₀ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun l => hc.continuousOn.integrableOn_compact (μ := μ₀)
        (sourceJacquetValuationShell_isCompact K P (l : ℤ))) hsummable
  have h := hball.union hshell
  rwa [sourceKPCoupledTameShells_cover K P, integrableOn_univ] at h

end
end ArtinMatthews
