module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Potential
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Poisson


set_option backward.privateInPublic true
@[expose] public section

/-! A normalized, genuine inverse of the Euclidean Laplacian on compact smooth data. -/

noncomputable section
open _root_.MeasureTheory Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

def poissonNormalization (m : ℕ) : ℝ :=
  (m : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m)

theorem poissonNormalization_ne_zero {m : ℕ} (hm : 3 ≤ m) : poissonNormalization m ≠ 0 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hV : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  exact mul_ne_zero (mul_ne_zero (by linarith) hV.ne') (by linarith)

def poissonPotential {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) : EuclideanSpace ℝ (Fin m) → ℝ :=
  (poissonNormalization m)⁻¹ • newtonianPotential f

theorem contDiff_poissonPotential {m : ℕ} (hm : 1 ≤ m) {k : ℕ∞}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ k f) (hfc : HasCompactSupport f) :
    ContDiff ℝ k (poissonPotential f) := by
  simpa only [poissonPotential, Pi.smul_apply] using!
    (contDiff_newtonianPotential hm f hf hfc).const_smul (poissonNormalization m)⁻¹

theorem laplacian_poissonPotential {m : ℕ} (hm : 3 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) :
    (laplacian (poissonPotential f) : EuclideanSpace ℝ (Fin m) → ℝ) x = f x := by
  rw [poissonPotential, laplacian_smul _
    (contDiff_newtonianPotential (show 1 ≤ m by omega) f hf hfc).contDiffAt,
    laplacian_newtonianPotential (show 2 ≤ m by omega) f hf hfc x]
  change (poissonNormalization m)⁻¹ * (poissonNormalization m * f x) = f x
  rw [← mul_assoc, inv_mul_cancel₀ (poissonNormalization_ne_zero hm), one_mul]

end OAI.Analysis.PDE.Schauder
