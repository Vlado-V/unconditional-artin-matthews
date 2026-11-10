module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Mollification
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Bilinear
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MollificationDerivatives
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Poisson
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Representation


set_option backward.privateInPublic true
@[expose] public section

/-! The sharp compact-support Schauder estimate requires only C² of the solution. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter InnerProductSpace Laplacian
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem continuous_laplacian_of_two {m : ℕ} (u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : ContDiff ℝ 2 u) : Continuous (laplacian u) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have he : laplacian u = fun x => ∑ i : Fin m, fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) := funext (laplacian_coordinate u)
  rw [he]
  exact continuous_finsetSum _ fun i _ =>
    ((hD.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const

theorem laplacian_smoothData {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    laplacian (smoothData φ u) = smoothData φ (laplacian u) := by
  funext x
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hDD : Continuous (fderiv ℝ (fderiv ℝ u)) := hD.continuous_fderiv one_ne_zero
  have hi (i : Fin m) : Integrable (fun y => φ.normed volume y *
      fderiv ℝ (fderiv ℝ u) (x - y) (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) :=
    φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ)
      φ.continuous_normed ((hDD.clm_apply continuous_const).clm_apply continuous_const).locallyIntegrable x
  rw [laplacian_coordinate]
  simp_rw [second_fderiv_smoothData φ u hu huc]
  simp only [smoothData, scalarConvolution]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [laplacian_coordinate, Finset.mul_sum]

theorem compact_schauder_estimate_C2 {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 u → HasCompactSupport u → ∀ H, 0 ≤ H →
      (∀ x y, |laplacian u x - laplacian u y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      ‖fderiv ℝ (fderiv ℝ u) z - fderiv ℝ (fderiv ℝ u) x‖ ≤ C * H * ‖z - x‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := compact_schauder_estimate hm hα hα1
  refine ⟨(m : ℝ) * m * C + 1, by positivity, ?_⟩
  intro u hu huc H hH hh x z
  have hk (k : ℕ) : ‖fderiv ℝ (fderiv ℝ (smoothData (standardMollifier m k) u)) z -
      fderiv ℝ (fderiv ℝ (smoothData (standardMollifier m k) u)) x‖ ≤ C * H * ‖z - x‖ ^ α := by
    apply hb _ ((contDiff_smoothData _ u hu.continuous).of_le (by simp))
      (hasCompactSupport_smoothData _ u huc) H hH
    intro a b
    rw [laplacian_smoothData _ u hu huc]
    exact smoothData_holder _ _ (continuous_laplacian_of_two u hu) hh a b
  have he (i j : Fin m) : |(fderiv ℝ (fderiv ℝ u) z - fderiv ℝ (fderiv ℝ u) x)
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤ C * H * ‖z - x‖ ^ α := by
    have ht := ((second_fderiv_smoothData_tendsto u hu huc z
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))).sub
      (second_fderiv_smoothData_tendsto u hu huc x
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))).abs
    have hb' (k : ℕ) := (euclidean_bilinear_entry_le_norm
      (fderiv ℝ (fderiv ℝ (smoothData (standardMollifier m k) u)) z -
       fderiv ℝ (fderiv ℝ (smoothData (standardMollifier m k) u)) x) i j).trans (hk k)
    simpa using le_of_tendsto ht (Eventually.of_forall fun k => by simpa using hb' k)
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, |(fderiv ℝ (fderiv ℝ u) z - fderiv ℝ (fderiv ℝ u) x)
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| := euclidean_bilinear_norm_le_sum _
    _ ≤ ∑ i : Fin m, ∑ j : Fin m, C * H * ‖z - x‖ ^ α :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
    _ = (m : ℝ) * m * C * H * ‖z - x‖ ^ α := by simp; ring
    _ ≤ ((m : ℝ) * m * C + 1) * H * ‖z - x‖ ^ α := by gcongr; linarith

end OAI.Analysis.PDE.Schauder
