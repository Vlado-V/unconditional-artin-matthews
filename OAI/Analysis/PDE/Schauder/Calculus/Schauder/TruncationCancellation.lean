module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Truncation
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Cancellation
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Poisson
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RegularizedMass


set_option backward.privateInPublic true
@[expose] public section

/-! The radially truncated Newtonian Hessian still has zero mean on every centered ball. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped BigOperators
namespace OAI.Analysis.PDE.Schauder

theorem radialCutoff_eq_of_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) {x y : E} (h : ‖x‖ = ‖y‖) : radialCutoff r x = radialCutoff r y := by
  simp only [radialCutoff, norm_smul, h]

theorem truncatedNewtonianEntry_coordinate {m : ℕ} (i j : Fin m) {r : ℝ} (hr : 0 < r)
    (y : EuclideanSpace ℝ (Fin m)) :
    truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r y =
      (1 - radialCutoff r y) * ((2 - (m : ℝ)) * ‖y‖ ^ (-(m : ℝ)) * (if i = j then 1 else 0) +
        (m : ℝ) * (m - 2) * ‖y‖ ^ (-(m : ℝ) - 2) * y i * y j) := by
  by_cases hy : y = 0
  · subst y
    simp [truncatedNewtonianEntry,
      radialCutoff_one hr (by simpa using hr.le : ‖(0 : EuclideanSpace ℝ (Fin m))‖ ≤ r)]
  · rw [truncatedNewtonianEntry, newtonianEntry_coordinate i j y hy]

theorem truncatedNewtonianEntry_ball_offDiagonal {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) r y) = 0 := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrRight 2 fun k =>
      if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ
  let K := truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = -y i := by simp [e]
  have hej (y : EuclideanSpace ℝ (Fin m)) : e y j = y j := by simp [e, Ne.symm hij]
  have hK (y : EuclideanSpace ℝ (Fin m)) : K (e y) = -K y := by
    dsimp [K]
    rw [truncatedNewtonianEntry_coordinate i j hr, truncatedNewtonianEntry_coordinate i j hr,
      radialCutoff_eq_of_norm_eq r (e.norm_map y), e.norm_map, hei, hej, ite_eq_right hij]
    ring
  have he := MeasureTheory.integral_comp e ((ball 0 R).indicator K)
  have heq : (fun y => (ball 0 R).indicator K (e y)) = fun y => -((ball 0 R).indicator K y) := by
    funext y
    by_cases hy : ‖y‖ < R <;> simp [Set.indicator, e.norm_map, hy, hK]
  rw [heq, integral_neg, integral_indicator measurableSet_ball] at he
  change (∫ y in ball 0 R, K y) = 0
  linarith

theorem truncatedNewtonianEntry_ball_diag_eq {m : ℕ} (i j : Fin m) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) r y) =
    ∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) r y := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  let K (i : Fin m) := truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) r
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = y j := by
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have hK (y : EuclideanSpace ℝ (Fin m)) : K i (e y) = K j y := by
    dsimp [K]
    rw [truncatedNewtonianEntry_coordinate i i hr, truncatedNewtonianEntry_coordinate j j hr,
      radialCutoff_eq_of_norm_eq r (e.norm_map y), e.norm_map, hei]
    simp only [ite_true]
  have he := MeasureTheory.integral_comp e ((ball 0 R).indicator (K i))
  have heq : (fun y => (ball 0 R).indicator (K i) (e y)) = (ball 0 R).indicator (K j) := by
    funext y
    by_cases hy : ‖y‖ < R <;> simp [Set.indicator, e.norm_map, hy, hK]
  rw [heq, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at he
  exact he.symm

theorem truncatedNewtonianEntry_ball {m : ℕ} (i j : Fin m) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) r y) = 0 := by
  by_cases hij : i = j
  · subst j
    let K (j : Fin m) := truncatedNewtonianEntry m (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r
    have hi (j : Fin m) : IntegrableOn (K j) (ball 0 R) :=
      integrableOn_continuous_ball _ (contDiff_truncatedNewtonianEntry m _ _ hr).continuous R
    have htrace (y : EuclideanSpace ℝ (Fin m)) : ∑ j, K j y = 0 := by
      by_cases hy : y = 0
      · subst y
        simp [K, truncatedNewtonianEntry,
          radialCutoff_one hr (by simpa using hr.le : ‖(0 : EuclideanSpace ℝ (Fin m))‖ ≤ r)]
      · dsimp [K, truncatedNewtonianEntry]
        rw [← Finset.mul_sum, newtonianEntry_trace hy, mul_zero]
    have hsum : (m : ℝ) * (∫ y in ball 0 R, K i y) = 0 := by
      calc
        _ = ∑ j : Fin m, ∫ y in ball 0 R, K j y := by
          dsimp [K]
          simp_rw [truncatedNewtonianEntry_ball_diag_eq _ i hr R]
          simp
        _ = ∫ y in ball 0 R, ∑ j : Fin m, K j y :=
          (MeasureTheory.integral_finsetSum Finset.univ fun j _ => hi j).symm
        _ = 0 := by simp [htrace]
    exact (mul_eq_zero.mp hsum).resolve_left (by exact_mod_cast (show m ≠ 0 by have := i.isLt; omega))
  · exact truncatedNewtonianEntry_ball_offDiagonal i j hij hr R

end OAI.Analysis.PDE.Schauder
