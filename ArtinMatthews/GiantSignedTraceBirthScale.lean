module

public import ArtinMatthews.GiantSignedSourceDoubledVisit
public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedTraceGhostAbsolute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Doubling a ghost birth coefficient multiplies the actual ordered
batch contribution by two to the batch size, leaving every other factor. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedGhostMoveCoefficient_birth_scale {P : Finset ℕ} (ν : P → ℝ)
    (A C D z : ℂ) (m : GiantSignedGroupMemory P) (r : GiantSignedGhostMoves m) :
    giantSignedGhostMoveCoefficient ν A (z*C) D m r =
      z^r.2.1 * giantSignedGhostMoveCoefficient ν A C D m r := by
  unfold giantSignedGhostMoveCoefficient
  split_ifs
  · rw [mul_pow]
    ring
  · exact (mul_zero _).symm

theorem giantSignedGhostMemoryMoveCoefficient_birth_scale {B : Type*} [Fintype B]
    {PB : B → Finset ℕ} (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ) (z : ℂ)
    (m : GiantSignedMemory PB) (r : GiantSignedGhostMemoryMoves m) :
    giantSignedGhostMemoryMoveCoefficient ν A (fun g => z*C g) D m r =
      z^(∑ g, (r g).2.1) * giantSignedGhostMemoryMoveCoefficient ν A C D m r := by
  simp only [giantSignedGhostMemoryMoveCoefficient, giantSignedGhostProductMoveCoefficient]
  simp_rw [giantSignedGhostMoveCoefficient_birth_scale]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

universe u
variable {S B : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}

def giantSignedDoubledVisitTraceRow (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ) :
    GiantSignedTraceRow.{u,u} (GiantSignedState PS PB M) :=
  giantSignedGhostTraceRow ν (fun _ => (|q / ρ^2| : ℝ))
    (fun g => (2 * |-(1-q) * V g / ρ| : ℝ)) (fun _ => (|-(1-q) / ρ| : ℝ))

theorem giantSignedDoubledVisitTraceRow_apply (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) :
    giantSignedTraceRowApply (giantSignedDoubledVisitTraceRow ν V q ρ) f =
      giantSignedSourceDoubledVisit PS ν V q ρ f := rfl

theorem giantSignedDoubledVisitTraceRow_coefficient (ν : ∀ g, PB g → ℝ)
    (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ) (s : GiantSignedState PS PB M)
    (r : GiantSignedGhostMemoryMoves s.2.2) :
    (giantSignedDoubledVisitTraceRow ν V q ρ).coefficient s r =
      (2:ℂ)^(∑ g, (r g).2.1) * (‖(giantSignedVisitTraceRow ν V q ρ).coefficient s r‖ : ℂ) := by
  let A : B → ℂ := fun _ => ((q / ρ^2 : ℝ) : ℂ)
  let C : B → ℂ := fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ)
  let D : B → ℂ := fun _ => ((-(1-q) / ρ : ℝ) : ℂ)
  have he := giantSignedGhostMemoryMoveCoefficient_birth_scale ν (fun g => (‖A g‖ : ℂ))
    (fun g => (‖C g‖ : ℂ)) (fun g => (‖D g‖ : ℂ)) 2 s.2.2 r
  rw [← giantSignedGhostMemoryMoveCoefficient_norm ν hν A C D] at he
  simpa only [giantSignedDoubledVisitTraceRow, giantSignedVisitTraceRow, giantSignedGhostTraceRow,
    A, C, D, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul, Complex.ofReal_ofNat] using he

end
end ArtinMatthews
