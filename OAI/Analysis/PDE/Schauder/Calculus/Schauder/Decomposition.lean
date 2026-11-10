module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.NearCutoff
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Convolution
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Potential
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Truncation
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialHessian
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RegularizedMass
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TruncationCancellation


set_option backward.privateInPublic true
@[expose] public section

/-! Exact near/far decomposition of the actual Newtonian Hessian. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem compensated_ball_split {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) {r R : ℝ} (hr : 0 < r) (hR : 2 * r ≤ R)
    (hsp : Function.support (fun y => f (x - y)) ⊆ ball 0 R) :
    (∫ y in ball 0 R, compensatedNewtonianEntry f x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y) =
      nearSingularPart f (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r x +
      scalarConvolution (truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) r) f x := by
  let v : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i (1 : ℝ)
  let w : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single j (1 : ℝ)
  let N := fun y => radialCutoff r y * compensatedNewtonianEntry f x v w y
  let K := truncatedNewtonianEntry m v w r
  let F := fun y => K y * f (x - y)
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf one_ne_zero
  have hh : ∀ y, |f (x - y) - f x| ≤ (C : ℝ) * ‖y‖ ^ (1 : ℝ) := by
    intro y
    have he : x - y - x = -y := by abel
    simpa [dist_eq_norm, he] using hC.dist_le_mul (x - y) x
  have hN : Integrable N := integrable_nearSingularPart hm f hf.continuous.measurable x v w hr C.coe_nonneg zero_lt_one hh
  have hK : Continuous K := (contDiff_truncatedNewtonianEntry m v w hr).continuous
  have hFc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  have hF : Integrable F := (hK.mul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hFc.mul_left
  have hKi : IntegrableOn K (ball 0 R) := integrableOn_continuous_ball K hK R
  have he : compensatedNewtonianEntry f x v w = fun y => N y + F y - f x * K y := by
    funext y
    simp only [N, F, K, truncatedNewtonianEntry, compensatedNewtonianEntry,
      finrank_euclideanSpace_fin, newtonianEntry]
    ring
  have hNball : (∫ y in ball 0 R, N y) = nearSingularPart f v w r x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hn : 2 * r ≤ ‖y‖ := hR.trans (le_of_not_gt (by simpa using hy))
    simp only [N, radialCutoff_zero hr hn, zero_mul]
  have hFball : (∫ y in ball 0 R, F y) = scalarConvolution K f x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hz : f (x - y) = 0 := by contrapose! hy; exact hsp hy
    simp [F, hz]
  change (∫ y in ball 0 R, compensatedNewtonianEntry f x v w y) = _
  have hNF : IntegrableOn (fun y => N y + F y) (ball 0 R) := hN.integrableOn.add hF.integrableOn
  have hconst : IntegrableOn (fun y => f x * K y) (ball 0 R) := hKi.const_mul _
  rw [he, integral_sub hNF hconst,
    integral_add hN.integrableOn hF.integrableOn, integral_const_mul, hNball, hFball]
  have hz : (∫ y in ball 0 R, K y) = 0 := truncatedNewtonianEntry_ball i j hr R
  rw [hz, mul_zero, sub_zero]

theorem newtonianPotential_hessian_near_far {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
      nearSingularPart f (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r x +
      scalarConvolution (truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) r) f x +
      f x * (if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0) := by
  have hgc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨R, hR, hsp⟩ := hgc.isCompact.isBounded.subset_ball_lt (2 * r) 0
  have hsp' : Function.support (fun y => f (x - y)) ⊆ ball 0 R := subset_closure.trans hsp
  rw [newtonianPotential_hessian hm f hf hfc x (by linarith) hsp',
    compensated_ball_split (show 1 ≤ m by omega) f (hf.of_le (by norm_num)) hfc x i j hr hR.le hsp']

end OAI.Analysis.PDE.Schauder
