module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Polar integration on a Euclidean ball, with its exact volume normalization. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem integral_ball_radial {m : ℕ} (hm : 1 ≤ m) (g : ℝ → ℝ) (R : ℝ) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) R, g ‖y‖) =
      (m : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
        ∫ t in Ioo (0 : ℝ) R, t ^ (m - 1) * g t := by
  let E := EuclideanSpace ℝ (Fin m)
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    change 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin m))
    simpa using (show 0 < m by omega))
  have he := integral_fun_norm_addHaar (volume : Measure E) ((Iio R).indicator g)
  have hspace : (fun y : E => (Iio R).indicator g ‖y‖) = (ball (0 : E) R).indicator (fun y => g ‖y‖) := by
    funext y
    by_cases hy : ‖y‖ < R <;> simp [hy]
  have hscalar (t : ℝ) : t ^ (m - 1) • (Iio R).indicator g t =
      (Iio R).indicator (fun t => t ^ (m - 1) * g t) t := by
    by_cases ht : t < R <;> simp [ht, smul_eq_mul]
  rw [hspace, integral_indicator measurableSet_ball] at he
  simp only [E, finrank_euclideanSpace_fin, hscalar, nsmul_eq_mul, smul_eq_mul] at he
  rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio] at he
  simpa only [mul_assoc] using he

end OAI.Analysis.PDE.Schauder
