module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelScale
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
public import Mathlib.Order.CompletePartialOrder
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.NearField
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialHessian


set_option backward.privateInPublic true
@[expose] public section

/-! The Newtonian potential genuinely solves the Poisson equation. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
open scoped BigOperators
namespace OAI.Analysis.PDE.Schauder

theorem laplacian_coordinate {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    (laplacian f : EuclideanSpace ℝ (Fin m) → ℝ) x =
      ∑ i : Fin m, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ)) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin m) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  simp only [EuclideanSpace.basisFun_apply]
  rfl

theorem newtonianEntry_trace {m : ℕ} {y : EuclideanSpace ℝ (Fin m)} (hy : y ≠ 0) :
    (∑ i : Fin m, newtonianEntry m (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) y) = 0 := by
  have h := laplacian_newtonianKernel hy
  simpa only [finrank_euclideanSpace_fin, laplacian_coordinate, newtonianEntry, newtonianSecond] using h

theorem laplacian_newtonianPotential {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) :
    (laplacian (newtonianPotential f) : EuclideanSpace ℝ (Fin m) → ℝ) x =
      (m : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) * f x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hgc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨R, hR, hsp⟩ := hgc.isCompact.isBounded.subset_ball_lt 0 0
  have hsp' : Function.support (fun y => f (x - y)) ⊆ ball 0 R := subset_closure.trans hsp
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf (by norm_num)
  have hh : ∀ y, |f (x - y) - f x| ≤ (C : ℝ) * ‖y‖ ^ (1 : ℝ) := by
    intro y
    have he : x - y - x = -y := by abel
    simpa [dist_eq_norm, he] using hC.dist_le_mul (x - y) x
  have hi (i : Fin m) : IntegrableOn (compensatedNewtonianEntry f x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) (ball 0 R) :=
    integrableOn_compensatedNewtonianEntry f x _ _ (by simpa using (show 1 ≤ m by omega))
      hf.continuous.measurable C.coe_nonneg zero_lt_one hh volume R
  have hz : (∫ y in ball 0 R, ∑ i : Fin m, compensatedNewtonianEntry f x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) y) = 0 := by
    apply integral_eq_zero_of_ae
    have hzero : ∀ᵐ y : EuclideanSpace ℝ (Fin m) ∂volume.restrict (ball 0 R), y ≠ 0 := by
      apply ae_restrict_of_ae
      rw [ae_iff]; simp
    filter_upwards [hzero] with y hy
    simp only [compensatedNewtonianEntry, finrank_euclideanSpace_fin, ← Finset.mul_sum]
    change (f (x - y) - f x) * (∑ i : Fin m, newtonianEntry m
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) y) = 0
    rw [newtonianEntry_trace hy, mul_zero]
  rw [laplacian_coordinate]
  simp_rw [newtonianPotential_hessian hm f hf hfc x hR hsp', ite_true]
  rw [Finset.sum_add_distrib, ← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hi i), hz]
  simp only [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end OAI.Analysis.PDE.Schauder
