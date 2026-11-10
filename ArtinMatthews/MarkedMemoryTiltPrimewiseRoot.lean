module

public import ArtinMatthews.MarkedMemoryTiltPrimewiseActual
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

/-! The primewise signed expansion is the actual finite SL₂ root average
of literal first-row vanishing tests at the primitive integer positions. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

theorem markedMemoryPrimeFactor_complex {N : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (A : Finset (Fin (N+1))) (η : Fin (N+1) → ℝ) (line : Fin (N+1) → Λ) :
    (markedMemoryPrimeFactor A η line : ℂ) = (Fintype.card Λ : ℂ)⁻¹ *
      ∑ ℓ : Λ, (((∏ j ∈ A, (markedLineHit line j ℓ : ℝ)) *
        ∏ j ∈ Finset.univ \ A, (1-η j*markedLineHit line j ℓ)) : ℝ) := by
  unfold markedMemoryPrimeFactor
  push_cast
  ring

def markedMemoryRootHit (p : Nat.Primes)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ))) (z : ℤ × ℤ) : ℝ :=
  if g 0 0 * (z.1 : ZMod (p : ℕ)) + g 0 1 * (z.2 : ZMod (p : ℕ)) = 0 then 1 else 0

theorem markedMemoryRootHit_eq (p : Nat.Primes) {N : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ)))
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2) (j : Fin (N+1)) :
    markedMemoryRootHit p g (z j) =
      markedLineHit (markedMemoryPositionLines p z hz) j (markedMatrixKernelLine g) := by
  have hiff : g 0 0 * ((z j).1 : ZMod (p : ℕ)) + g 0 1 * ((z j).2 : ZMod (p : ℕ)) = 0 ↔
      markedMemoryPositionLines p z hz j = markedMatrixKernelLine g := by
    simpa only [markedMemoryPositionLines, markedPrimePositionLine,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      markedMatrixKernelLine_incidence g ![(z j).1, (z j).2]
        (markedPrimePosition_nonzero (p : ℕ) (z j) (hz j))
  by_cases h : g 0 0 * ((z j).1 : ZMod (p : ℕ)) + g 0 1 * ((z j).2 : ZMod (p : ℕ)) = 0
  · simp only [markedMemoryRootHit, ite_eq_left h, markedLineHit, (hiff.mp h).symm, ite_true]
  · have hn : markedMatrixKernelLine g ≠ markedMemoryPositionLines p z hz j :=
      fun hh => h (hiff.mpr hh.symm)
    simp only [markedMemoryRootHit, ite_eq_right h, markedLineHit, ite_eq_right hn]

/-- Actual uniform root-matrix law for the full primewise physical factor,
with active divisibility tests and inactive q_j damping both present. -/
theorem markedMemoryProjectiveFactor_root_average (p : Nat.Primes) {N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ j, IsCoprime (z j).1 (z j).2)
    (A : Finset (Fin (N+1))) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ))) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ)),
        (((∏ j ∈ A, markedMemoryRootHit p g (z j)) *
          ∏ j ∈ Finset.univ \ A, (1-markedMemoryEta q N j*markedMemoryRootHit p g (z j))) : ℝ)) =
      (markedMemoryProjectiveFactor p q z hz A : ℂ) := by
  let f : MarkedRawPrimeLine p → ℂ := fun ℓ =>
    (((∏ j ∈ A, (markedLineHit (markedMemoryPositionLines p z hz) j ℓ : ℝ)) *
      ∏ j ∈ Finset.univ \ A,
        (1-markedMemoryEta q N j*markedLineHit (markedMemoryPositionLines p z hz) j ℓ)) : ℝ)
  calc
    _ = (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ))) : ℂ)⁻¹ *
        ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ)), f (markedMatrixKernelLine g) := by
      congr 1
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [f, markedMemoryRootHit_eq p g z hz]
    _ = (((p : ℕ)+1 : ℕ) : ℂ)⁻¹ * ∑ ℓ : MarkedRawPrimeLine p, f ℓ :=
      marked_prime_root_kernel_line_average (p : ℕ) f
    _ = _ := by
      rw [markedMemoryProjectiveFactor, markedMemoryPrimeFactor_complex, markedMemoryPrimeLine_card]
      rw [Complex.ofReal_sum]

/-- The same true root average with the active set computed from the
actual path of typed prime labels, retaining every literal visit. -/
theorem markedMemoryProjectiveFactor_root_average_slots {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M N : ℕ} (slots : Fin (N+1) → MarkedRawActive P M)
    (p : Nat.Primes) (q : ℝ) (z : Fin (N+1) → ℤ × ℤ)
    (hz : ∀ j, IsCoprime (z j).1 (z j).2) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ))) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ)),
        (((∏ j ∈ markedMemoryActiveVisits slots p, markedMemoryRootHit p g (z j)) *
          ∏ j ∈ Finset.univ \ markedMemoryActiveVisits slots p,
            (1-markedMemoryEta q N j*markedMemoryRootHit p g (z j))) : ℝ)) =
      (markedMemoryProjectiveFactor p q z hz (markedMemoryActiveVisits slots p) : ℂ) :=
  markedMemoryProjectiveFactor_root_average p q z hz _

end ArtinMatthews
