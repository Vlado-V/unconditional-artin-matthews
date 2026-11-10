module

public import ArtinMatthews.GiantSignedChronologicalLifespanCoefficient
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


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual ghost batch may be ordered independently. The resulting
multiplicity cancels exactly the chronological inverse factorials. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B] {PB : B → Finset ℕ} {n : ℕ}
    {A : (g : B) → PB g → Finset (Fin (n+1))}
    (c : ∀ g p, GiantSignedResidueLifespanChoice (A g p))

abbrev GiantSignedLifespanBirthOrderSchedule :=
  (v : Fin (n+1)) → (g : B) →
    Fin (giantSignedGhostVisitBorn (c g) v).card ≃ ↥(giantSignedGhostVisitBorn (c g) v)

theorem giantSignedLifespanBirthOrderSchedule_card :
    Fintype.card (GiantSignedLifespanBirthOrderSchedule c) =
      ∏ v, ∏ g, (giantSignedGhostVisitBorn (c g) v).card.factorial := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro v _
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun g _ => giantSignedGhostVisitBirthOrder_card (c g) v

theorem giantSignedLifespanBirthOrderSchedule_card_mul_factor :
    (Fintype.card (GiantSignedLifespanBirthOrderSchedule c) : ℂ) *
      giantSignedChronologicalBirthFactor (fun v g => (giantSignedGhostVisitBorn (c g) v).card) = 1 := by
  have hn : (∏ v, ∏ g, (giantSignedGhostVisitBorn (c g) v).card.factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ =>
      Finset.prod_ne_zero_iff.mpr fun g _ => Nat.factorial_ne_zero _
  have hc : ((∏ v, ∏ g, (giantSignedGhostVisitBorn (c g) v).card.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hn
  have hinv : giantSignedChronologicalBirthFactor (fun v g => (giantSignedGhostVisitBorn (c g) v).card) =
      ((∏ v, ∏ g, (giantSignedGhostVisitBorn (c g) v).card.factorial : ℕ) : ℂ)⁻¹ := by
    simp only [giantSignedChronologicalBirthFactor, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [giantSignedLifespanBirthOrderSchedule_card c, hinv, mul_inv_cancel₀ hc]

theorem giantSignedLifespanBirthOrderSchedule_sum_factor (z : ℂ) :
    (∑ _order : GiantSignedLifespanBirthOrderSchedule c,
      giantSignedChronologicalBirthFactor (fun v g => (giantSignedGhostVisitBorn (c g) v).card) * z) = z := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    giantSignedLifespanBirthOrderSchedule_card_mul_factor c, one_mul]

end
end ArtinMatthews
