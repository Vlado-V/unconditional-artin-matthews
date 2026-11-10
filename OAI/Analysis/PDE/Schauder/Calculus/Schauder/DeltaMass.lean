module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Regularized
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RegularizedMass


set_option backward.privateInPublic true
@[expose] public section

/-! The point-mass coefficient in the distributional Newtonian Hessian. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem newtonian_radial_flux_at_zero (m : ℕ) {R : ℝ} (hR : 0 < R) :
    2 * (1 - (m : ℝ) / 2) * R ^ m * (R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1) = 2 - m := by
  have he : (R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1) = R ^ (-(m : ℝ)) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
    congr 1
    push_cast
    ring
  rw [he, ← Real.rpow_natCast R m]
  calc
    _ = 2 * (1 - (m : ℝ) / 2) * (R ^ (m : ℝ) * R ^ (-(m : ℝ))) := by ring
    _ = 2 * (1 - (m : ℝ) / 2) * 1 := by
      rw [← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero]
    _ = _ := by ring

theorem tendsto_shiftedNewtonian_mass {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 < R)
    (i j : Fin m) :
    Tendsto (fun s : ℝ => ∫ y in ball 0 R,
      shiftedRadialHessian (1 - (m : ℝ) / 2) s y
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) (𝓝[>] 0)
      (𝓝 (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0)) := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hp : ContinuousAt (fun s : ℝ => (s + R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1)) 0 :=
      (continuousAt_id.add continuousAt_const).rpow_const
        (Or.inl (by simpa using (sq_pos_of_pos hR).ne'))
    have hc : ContinuousAt (fun s : ℝ => volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
        (2 * (1 - (m : ℝ) / 2) * R ^ m * (s + R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1))) 0 :=
      continuousAt_const.mul (continuousAt_const.mul hp)
    have ht := hc.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have ht' : Tendsto (fun s : ℝ => volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
        (2 * (1 - (m : ℝ) / 2) * R ^ m * (s + R ^ 2) ^ ((1 - (m : ℝ) / 2) - 1)))
        (𝓝[>] 0) (𝓝 (volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m))) := by
      simpa only [zero_add, newtonian_radial_flux_at_zero m hR] using ht
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (shiftedRadialHessian_ball_mass hm _ hs hR.le i).symm
  · simp only [ite_eq_right hij]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun s => (shiftedRadialHessian_ball_offDiagonal _ s R i j hij).symm

end OAI.Analysis.PDE.Schauder
