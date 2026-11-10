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


set_option backward.privateInPublic true
@[expose] public section

/-! Radial second moments and the symmetry behind Newtonian kernel cancellation. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped BigOperators
namespace OAI.Analysis.PDE.Schauder

def radialMoment {m : ℕ} (ρ : ℝ → ℝ) (i j : Fin m) : ℝ :=
  ∫ y : EuclideanSpace ℝ (Fin m), ρ ‖y‖ * y i * y j

theorem radialMoment_offDiagonal {m : ℕ} (ρ : ℝ → ℝ) (i j : Fin m) (hij : i ≠ j) :
    radialMoment ρ i j = 0 := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrRight 2 fun k =>
      if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = -y i := by simp [e]
  have hej (y : EuclideanSpace ℝ (Fin m)) : e y j = y j := by simp [e, hij.symm]
  have he := MeasureTheory.integral_comp e
    (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * y i * y j)
  simp only [e.norm_map, hei, hej] at he
  have hf : (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * -y i * y j) =
      fun y => -(ρ ‖y‖ * y i * y j) := by funext y; ring
  rw [hf, integral_neg] at he
  dsimp [radialMoment]
  linarith

theorem radialMoment_diagonal_eq {m : ℕ} (ρ : ℝ → ℝ) (i j : Fin m) :
    radialMoment ρ i i = radialMoment ρ j j := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = y j := by
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have he := MeasureTheory.integral_comp e
    (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * y i * y i)
  simp only [e.norm_map, hei] at he
  exact he.symm

theorem radialMoment_trace {m : ℕ} (ρ : ℝ → ℝ)
    (hint : ∀ i : Fin m, Integrable (fun y : EuclideanSpace ℝ (Fin m) => ρ ‖y‖ * y i * y i))
    (i : Fin m) :
    (m : ℝ) * radialMoment ρ i i =
      ∫ y : EuclideanSpace ℝ (Fin m), ρ ‖y‖ * ‖y‖ ^ 2 := by
  calc
    (m : ℝ) * radialMoment ρ i i = ∑ j : Fin m, radialMoment ρ j j := by
      simp_rw [radialMoment_diagonal_eq ρ _ i]
      simp
    _ = ∫ y : EuclideanSpace ℝ (Fin m), ∑ j : Fin m, ρ ‖y‖ * y j * y j := by
      exact (MeasureTheory.integral_finsetSum Finset.univ fun j _ => hint j).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [EuclideanSpace.real_norm_sq_eq]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

end OAI.Analysis.PDE.Schauder
