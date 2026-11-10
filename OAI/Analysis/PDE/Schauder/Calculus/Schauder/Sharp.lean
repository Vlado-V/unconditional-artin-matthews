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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Decomposition
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.FarLipschitz


set_option backward.privateInPublic true
@[expose] public section

/-! The exponent-preserving Newtonian Schauder estimate for compact C² data.
The estimate is on the actual second Fréchet derivative, not a formal singular integral. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem schauder_scale_identity {r : ℝ} (hr : 0 < r) (α : ℝ) :
    (r / 2) ^ (α - 1) * r = (1 / 2 : ℝ) ^ (α - 1) * r ^ α := by
  rw [show r / 2 = (1 / 2 : ℝ) * r by ring,
    Real.mul_rpow (by positivity) hr.le, mul_assoc,
    ← Real.rpow_add_one hr.ne', sub_add_cancel]

theorem newtonianPotential_hessian_entry_holder {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (i j : Fin m) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 f → HasCompactSupport f → ∀ H, 0 ≤ H →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      |fderiv ℝ (fderiv ℝ (newtonianPotential f)) z
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) -
        fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤
        C * H * ‖z - x‖ ^ α := by
  let v : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i (1 : ℝ)
  let w : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single j (1 : ℝ)
  obtain ⟨B, hB, hfar⟩ := farConvolution_difference_bound (show 1 ≤ m by omega) v w
  let N : ℝ := newtonianSizeConstant m *
    rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α * (3 : ℝ) ^ α
  let F : ℝ := B * (1 / 2 : ℝ) ^ (α - 1) *
    rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α
  let D : ℝ := if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0
  have hN : 0 ≤ N := mul_nonneg (mul_nonneg (newtonianSizeConstant_nonneg m)
    (rieszBallMass_nonneg _ _)) (Real.rpow_nonneg (by norm_num) _)
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (by norm_num) _))
    (rieszTailMass_nonneg _ _)
  refine ⟨2 * N + F + |D| + 1, by positivity, ?_⟩
  intro f hf hfc H hH hh x z
  by_cases hxz : z = x
  · simp [hxz, Real.zero_rpow hα.ne']
  have hr : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  let r := ‖z - x‖
  have hinc (a : EuclideanSpace ℝ (Fin m)) : ∀ y, |f (a - y) - f a| ≤ H * ‖y‖ ^ α := by
    intro y
    have he : a - y - a = -y := by abel
    simpa only [he, norm_neg] using hh (a - y) a
  have hnear (a : EuclideanSpace ℝ (Fin m)) : |nearSingularPart f v w r a| ≤ N * H * r ^ α := by
    have hn := nearSingularPart_bound (show 1 ≤ m by omega) f a v w hr hH hα (hinc a)
    have hv : ‖v‖ = 1 := by simp [v]
    have hw : ‖w‖ = 1 := by simp [w]
    rw [hv, hw, mul_one, mul_one, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.le] at hn
    simpa only [N, mul_assoc, mul_comm, mul_left_comm] using hn
  have hfd : |scalarConvolution (truncatedNewtonianEntry m v w r) f z -
      scalarConvolution (truncatedNewtonianEntry m v w r) f x| ≤ F * H * r ^ α := by
    have ht := hfar r α H hr hα1 hH f (hf.of_le (by norm_num)) hfc hh x z
    have he : (H * B * (r / 2) ^ (α - 1) * rieszTailMass
        (volume : Measure (EuclideanSpace ℝ (Fin m))) α) * r = F * H * r ^ α := by
      calc
        _ = H * B * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α *
            ((r / 2) ^ (α - 1) * r) := by ring
        _ = _ := by rw [schauder_scale_identity hr]; dsimp [F]; ring
    exact he ▸ ht
  have hd : |(f z - f x) * D| ≤ |D| * H * r ^ α := by
    rw [abs_mul]
    calc
      _ ≤ (H * r ^ α) * |D| := mul_le_mul_of_nonneg_right (hh z x) (abs_nonneg D)
      _ = _ := by ring
  change |fderiv ℝ (fderiv ℝ (newtonianPotential f)) z v w -
    fderiv ℝ (fderiv ℝ (newtonianPotential f)) x v w| ≤ _
  rw [newtonianPotential_hessian_near_far hm f hf hfc z i j hr,
    newtonianPotential_hessian_near_far hm f hf hfc x i j hr]
  change |nearSingularPart f v w r z + scalarConvolution (truncatedNewtonianEntry m v w r) f z + f z * D -
    (nearSingularPart f v w r x + scalarConvolution (truncatedNewtonianEntry m v w r) f x + f x * D)| ≤ _
  calc
    _ = |(nearSingularPart f v w r z - nearSingularPart f v w r x) +
        (scalarConvolution (truncatedNewtonianEntry m v w r) f z -
          scalarConvolution (truncatedNewtonianEntry m v w r) f x) + (f z - f x) * D| := by congr 1; ring
    _ ≤ (|nearSingularPart f v w r z| + |nearSingularPart f v w r x|) +
        |scalarConvolution (truncatedNewtonianEntry m v w r) f z -
          scalarConvolution (truncatedNewtonianEntry m v w r) f x| + |(f z - f x) * D| := by
      have h1 := abs_add_le
        (nearSingularPart f v w r z - nearSingularPart f v w r x +
          (scalarConvolution (truncatedNewtonianEntry m v w r) f z -
            scalarConvolution (truncatedNewtonianEntry m v w r) f x)) ((f z - f x) * D)
      have h2 := abs_add_le (nearSingularPart f v w r z - nearSingularPart f v w r x)
        (scalarConvolution (truncatedNewtonianEntry m v w r) f z -
          scalarConvolution (truncatedNewtonianEntry m v w r) f x)
      have h3 := abs_sub (nearSingularPart f v w r z) (nearSingularPart f v w r x)
      linarith only [h1, h2, h3]
    _ ≤ (2 * N + F + |D|) * H * r ^ α := by linarith [hnear z, hnear x]
    _ ≤ (2 * N + F + |D| + 1) * H * ‖z - x‖ ^ α := by
      dsimp [r]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hH)
        (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.PDE.Schauder
