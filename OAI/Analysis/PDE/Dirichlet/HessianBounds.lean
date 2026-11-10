module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Dirichlet.Derivative
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Dirichlet.SecondDerivative
public import OAI.LinearAlgebra.Moore.Inverse


set_option backward.privateInPublic true
@[expose] public section

open Set
open scoped ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem realHessian_trace_nonneg_of_quaternion {n : ℕ}
    {ψ : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hψ : ContDiffAt ℝ 2 ψ x)
    (hA : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosSemidef) :
    0 ≤ (realHessian ψ x).trace := by
  have hc := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  rw [OAI.LinearAlgebra.Moore.complexify_trace_real] at hc
  have ht := congrArg (fun q : Quaternion ℝ ↦ q.re)
    (quaternionHessian_trace OAI.Analysis.Calculus.Quaternion.fourSlots OAI.Analysis.Calculus.Quaternion.fourSlots_orthonormal hψ)
  simp [Matrix.trace] at ht
  have hre (t : Finset (Fin n)) :
      (∑ i ∈ t, quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x i i).re =
        ∑ i ∈ t, (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x i i).re := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih => simp [hi, ih]
  rw [hre] at ht
  rw [realHessian_trace]
  linarith

theorem norm_coordinateVector {m s : ℕ} (i : Fin m × Fin s) :
    ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

/-- A trace lower bound converts upper directional bounds into two-sided
entry bounds. The deliberately coarse constant is sufficient for compactness. -/
theorem realHessian_entry_abs_le {m s : ℕ} {ψ : CoordinateSpace m s → ℝ}
    {x : CoordinateSpace m s} (hψ : ContDiffAt ℝ 2 ψ x) {C : ℝ} (hC : 0 ≤ C)
    (htrace : 0 ≤ (realHessian ψ x).trace)
    (hupper : ∀ v : CoordinateSpace m s,
      (fderiv ℝ (fderiv ℝ ψ) x v) v ≤ C * ‖v‖ ^ 2)
    (i j : Fin m × Fin s) :
    |realHessian ψ x i j| ≤ ((Fintype.card (Fin m × Fin s) : ℝ) + 2) * C := by
  classical
  let H := realHessian ψ x
  let d : ℝ := Fintype.card (Fin m × Fin s)
  have hdiag (k : Fin m × Fin s) : H k k ≤ C := by
    simpa only [H, realHessian, norm_coordinateVector, one_pow, mul_one] using hupper (coordinateVector k)
  have hlower (k : Fin m × Fin s) : -d * C ≤ H k k := by
    have hs : ∑ a ∈ Finset.univ.erase k, H a a ≤ d * C := by
      calc
        ∑ a ∈ Finset.univ.erase k, H a a ≤ ∑ _a ∈ Finset.univ.erase k, C :=
          Finset.sum_le_sum fun a _ ↦ hdiag a
        _ ≤ ∑ _a : Fin m × Fin s, C :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset k Finset.univ) (fun _ _ _ ↦ hC)
        _ = d * C := by simp [d]
    have he : (∑ a ∈ Finset.univ.erase k, H a a) + H k k = H.trace := by
      exact Finset.sum_erase_add _ _ (Finset.mem_univ k)
    change 0 ≤ H.trace at htrace
    linarith
  have hnormp : ‖coordinateVector i + coordinateVector j‖ ≤ 2 := by
    simpa only [norm_coordinateVector, one_add_one_eq_two] using norm_add_le (coordinateVector i) (coordinateVector j)
  have hnormm : ‖coordinateVector i - coordinateVector j‖ ≤ 2 := by
    simpa only [norm_coordinateVector, one_add_one_eq_two] using norm_sub_le (coordinateVector i) (coordinateVector j)
  have hp := hupper (coordinateVector i + coordinateVector j)
  have hm := hupper (coordinateVector i - coordinateVector j)
  have hp' : C * ‖coordinateVector i + coordinateVector j‖ ^ 2 ≤ 4 * C := by
    have hs : ‖coordinateVector i + coordinateVector j‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (coordinateVector i + coordinateVector j)]
    nlinarith
  have hm' : C * ‖coordinateVector i - coordinateVector j‖ ^ 2 ≤ 4 * C := by
    have hs : ‖coordinateVector i - coordinateVector j‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (coordinateVector i - coordinateVector j)]
    nlinarith
  have hsym : H j i = H i j := by
    exact (hψ.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector j) (coordinateVector i)
  simp only [map_add, map_sub, add_apply, sub_apply] at hp hm
  change H i i + H j i + (H i j + H j j) ≤ _ at hp
  change H i i - H j i - (H i j - H j j) ≤ _ at hm
  rw [hsym] at hp hm
  have hi := hlower i
  have hj := hlower j
  change |H i j| ≤ (d + 2) * C
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem hessian_norm_le_of_entry_bound {m s : ℕ} (ψ : CoordinateSpace m s → ℝ)
    (x : CoordinateSpace m s) {C : ℝ} (hC : 0 ≤ C)
    (hentry : ∀ i j, |realHessian ψ x i j| ≤ C) :
    ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ (Fintype.card (Fin m × Fin s) : ℝ) ^ 2 * C := by
  classical
  let d : ℝ := Fintype.card (Fin m × Fin s)
  have hcoord (v : CoordinateSpace m s) (i : Fin m × Fin s) : |v i| ≤ ‖v‖ := by
    simpa [coordinateVector, EuclideanSpace.inner_single_left] using
      abs_real_inner_le_norm (coordinateVector i) v
  have hbound (v w : CoordinateSpace m s) :
      |(fderiv ℝ (fderiv ℝ ψ) x v) w| ≤ (d ^ 2 * C * ‖v‖) * ‖w‖ := by
    rw [← realHessian_bilinear ψ x v w]
    calc
      |∑ i, ∑ j, v i * realHessian ψ x i j * w j| ≤
          ∑ i, ∑ j, |v i * realHessian ψ x i j * w j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin m × Fin s, ∑ _j : Fin m × Fin s, ‖v‖ * C * ‖w‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simp only [abs_mul]
        exact mul_le_mul (mul_le_mul (hcoord v i) (hentry i j) (abs_nonneg _) (norm_nonneg _))
          (hcoord w j) (abs_nonneg _) (mul_nonneg (norm_nonneg _) hC)
      _ = (d ^ 2 * C * ‖v‖) * ‖w‖ := by simp [d]; ring
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sq_nonneg _) hC)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  exact hbound v w

/-- A full real-Hessian norm estimate from upper bounds in all directions,
using only nonnegativity of the quaternionic Hessian. -/
theorem hessian_norm_le_of_quaternion_and_upper {n : ℕ}
    {ψ : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hψ : ContDiffAt ℝ 2 ψ x)
    (hA : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosSemidef)
    {C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ v : CoordinateSpace n 4,
      (fderiv ℝ (fderiv ℝ ψ) x v) v ≤ C * ‖v‖ ^ 2) :
    ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ (Fintype.card (Fin n × Fin 4) : ℝ) ^ 2 *
      (((Fintype.card (Fin n × Fin 4) : ℝ) + 2) * C) := by
  apply hessian_norm_le_of_entry_bound ψ x (by positivity)
  exact realHessian_entry_abs_le hψ hC (realHessian_trace_nonneg_of_quaternion hψ hA) hupper

/-- The full interior real-Hessian estimate from the prescribed density and
boundary second derivatives. The dimension factor is not optimized. -/
theorem quaternionic_hessian_norm_estimate {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 4 ψ) (hr : ContDiff ℝ 2 r)
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    {m M r₀ L B : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hr₀ : 0 < r₀) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hdataBounds : ∀ x ∈ interior K, m ≤ F x ∧ F x ≤ M)
    (hconvex : ∀ x ∈ interior K,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x -
        r₀ • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hdata : ∀ v : CoordinateSpace n 4, ∀ x ∈ interior K,
      -L * ‖v‖ ^ 2 ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0)
    (hboundary : ∀ v : CoordinateSpace n 4, ∀ x ∈ K, x ∉ interior K →
      directionalDerivative (directionalDerivative ψ v) v x ≤ B * ‖v‖ ^ 2)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0)
    (hrneg : ∀ x ∈ K, r x ≤ 0) :
    ∀ x ∈ interior K, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤
      (Fintype.card (Fin n × Fin 4) : ℝ) ^ 2 *
        (((Fintype.card (Fin n × Fin 4) : ℝ) + 2) *
          (B - ((L * M) / (r₀ * (m / (2 * (M ^ 2 + 1))))) * r x)) := by
  intro x hx
  have hxK := interior_subset hx
  let κ := r₀ * (m / (2 * (M ^ 2 + 1)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcoef : 0 ≤ (L * M) / κ := div_nonneg (mul_nonneg hL hM) hκ.le
  have hC : 0 ≤ B - ((L * M) / κ) * r x := by
    have := mul_nonpos_of_nonneg_of_nonpos hcoef (hrneg x hxK)
    linarith
  apply hessian_norm_le_of_quaternion_and_upper (hψ.of_le (by norm_num)).contDiffAt
    (hA x hx).posSemidef hC
  intro v
  have hd : ∀ y ∈ interior K,
      -(L * ‖v‖ ^ 2) ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (y + t • v)))) 0 := by
    simpa only [neg_mul] using hdata v
  have hv := quaternionic_second_directional_estimate hn hK hψ hr hA heq v hm hM hr₀
    (mul_nonneg hL (sq_nonneg _)) hdataBounds hconvex hd (hboundary v) hrbd x hxK
  rw [directionalDerivative_twice (hψ.of_le (by norm_num))] at hv
  convert hv using 1 ; dsimp [κ] ; ring

end OAI.Analysis.PDE.Dirichlet
