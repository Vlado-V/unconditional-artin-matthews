module

public import ArtinMatthews.GiantSignedSmallTransferMemory
public import ArtinMatthews.GiantSignedSmallPermutationProducts
public import ArtinMatthews.GiantSignedSmallOmissionSize
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual source-slot averaging gives the rare-transfer probability.
The full pending memory is retained, and a degree budget is applied only in the last inequality. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

section RareTransfer
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J]
variable {P : S → Finset ℕ} {Q : J → Finset ℕ}
variable {kCopy ell : ℕ}

theorem giantSignedSmallRareTransfer_mean_le
    (hP : ∀ g q, q ∈ P g → q.Prime) (hQ : ∀ j q, q ∈ Q j → q.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hsep : ∀ g j, Disjoint (P g) (Q j))
    (a : MarkedPhysicalMarking P (kCopy + ell)) (ha : MarkedPhysicalMarkingDistinct a)
    (z : ℤ) (DBig : ℕ) (m : GiantSignedMemory Q)
    (hz : ∀ j i, (z : ZMod (m.2 j i).1.val) ≠ 0)
    (hbound : ∀ j i (U : GiantSignedSmallOmission S (kCopy + ell) ell),
      giantSignedSmallOmittedProduct a U < (m.2 j i).1.val) :
    (∑ σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)),
      if GiantSignedSmallMemoryAllows a z DBig m (giantSignedSmallPermutationOmission kCopy ell σ)
      then (1 : ℝ) else 0) / ((kCopy + ell).factorial : ℝ) ^ Fintype.card S ≤
        ((∑ j, m.1 j : ℕ) : ℝ) / (giantSignedSmallOmissionNumber S (kCopy + ell) ell : ℝ) := by
  classical
  rw [giantSignedSmallPermutationOmission_average kCopy ell
    (fun U : GiantSignedSmallOmission S (kCopy + ell) ell =>
      if GiantSignedSmallMemoryAllows a z DBig m U then (1 : ℝ) else 0)]
  have he : (∑ U : GiantSignedSmallOmission S (kCopy + ell) ell,
      if GiantSignedSmallMemoryAllows a z DBig m U then (1 : ℝ) else 0) =
        ((giantSignedSmallMemoryOmissions (ell := ell) a z DBig m).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, giantSignedSmallMemoryOmissions]
  rw [he]
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (giantSignedSmallMemoryOmissions_card_le Q hP hQ hdis hsep a ha z DBig m hz hbound))
    (Nat.cast_nonneg _)

def GiantSignedSmallSourceMemoryAllows
    (a : MarkedPhysicalMarking P (kCopy + ell)) (z : ℤ) (DBig : ℕ) (m : GiantSignedMemory Q)
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) : Prop :=
  ∃ j i,
    (m.2 j i).2 + ((z : ZMod (m.2 j i).1.val) * (DBig : ZMod (m.2 j i).1.val)) *
      (giantSignedSmallPermutationCopiedProduct a σ : ZMod (m.2 j i).1.val) = 0 ∧
      ¬ (m.2 j i).1.val ∣ DBig * giantSignedSmallPermutationCopiedProduct a σ

omit [Fintype J] [DecidableEq S] in
theorem giantSignedSmallSourceMemoryAllows_iff
    (hP : ∀ g q, q ∈ P g → q.Prime)
    (a : MarkedPhysicalMarking P (kCopy + ell)) (z : ℤ) (DBig : ℕ) (m : GiantSignedMemory Q)
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    GiantSignedSmallSourceMemoryAllows a z DBig m σ ↔
      GiantSignedSmallMemoryAllows a z DBig m (giantSignedSmallPermutationOmission kCopy ell σ) := by
  unfold GiantSignedSmallSourceMemoryAllows GiantSignedSmallMemoryAllows GiantSignedSmallTransferEvent
  simp only [giantSignedSmallPermutationCopied_eq hP]

theorem giantSignedSmallRareTransfer_source_bound
    (hP : ∀ g q, q ∈ P g → q.Prime) (hQ : ∀ j q, q ∈ Q j → q.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hsep : ∀ g j, Disjoint (P g) (Q j))
    (a : MarkedPhysicalMarking P (kCopy + ell)) (ha : MarkedPhysicalMarkingDistinct a)
    (kStep : ℕ) (hk : 0 < kStep) (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (DBig : ℕ) (m : GiantSignedMemory Q) (B : ℕ) (hB : (∑ j, m.1 j) ≤ B)
    (hstep : ∀ j i, kStep < (m.2 j i).1.val)
    (t q : ℝ) (hlabels : ∀ g i, (a g i : ℝ) ≤ Real.exp t)
    (hbudget : (ell : ℝ) * (Fintype.card S : ℝ) * t < q)
    (hprimeLower : ∀ j i, Real.exp q ≤ ((m.2 j i).1.val : ℝ)) :
    (∑ σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)),
      if GiantSignedSmallSourceMemoryAllows a (sign * kStep) DBig m σ then (1 : ℝ) else 0) /
        ((kCopy + ell).factorial : ℝ) ^ Fintype.card S ≤
      (B : ℝ) / (giantSignedSmallOmissionNumber S (kCopy + ell) ell : ℝ) := by
  have hmean := giantSignedSmallRareTransfer_mean_le hP hQ hdis hsep a ha (sign * kStep) DBig m
    (fun j i => giantSignedSignedStep_ne_zero_mod kStep hk (hstep j i) sign hsign)
    (fun j i U => giantSignedSmallOmittedProduct_lt_prime a t q hlabels hbudget (hprimeLower j i) U)
  have he : (∑ σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)),
      if GiantSignedSmallSourceMemoryAllows a (sign * kStep) DBig m σ then (1 : ℝ) else 0) =
      ∑ σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)),
        if GiantSignedSmallMemoryAllows a (sign * kStep) DBig m
          (giantSignedSmallPermutationOmission kCopy ell σ) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [giantSignedSmallSourceMemoryAllows_iff hP]
  rw [he]
  exact hmean.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hB) (Nat.cast_nonneg _))

end RareTransfer


universe u v

/-- The source exponent gap supplies one threshold for all small-group
carriers and all copy counts subject to the literal logarithmic count bound. -/
theorem giantSignedSmallRareTransfer_source_eventually (A : ℝ) (ell : ℕ)
    {b c : ℝ} (hbc : b < c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (S : Type u) [Fintype S] [DecidableEq S] (J : Type v) [Fintype J]
        (P : S → Finset ℕ) (Q : J → Finset ℕ) (kCopy : ℕ)
        (_ : ∀ g q, q ∈ P g → q.Prime) (_ : ∀ j q, q ∈ Q j → q.Prime)
        (_ : Pairwise (fun g h => Disjoint (P g) (P h)))
        (_ : ∀ g j, Disjoint (P g) (Q j))
        (a : MarkedPhysicalMarking P (kCopy + ell)) (_ : MarkedPhysicalMarkingDistinct a)
        (kStep : ℕ) (_ : 0 < kStep) (sign : ℤ) (_ : sign = 1 ∨ sign = -1)
        (DBig : ℕ) (m : GiantSignedMemory Q) (B : ℕ),
        (∑ j, m.1 j) ≤ B → (Fintype.card S : ℝ) ≤ A * Real.log L →
        (∀ j i, kStep < (m.2 j i).1.val) →
        (∀ g i, (a g i : ℝ) ≤ Real.exp (L ^ b)) →
        (∀ j i, Real.exp (L ^ c) ≤ ((m.2 j i).1.val : ℝ)) →
        (∑ σ : (g : S) → Equiv.Perm (Fin (kCopy + ell)),
          if GiantSignedSmallSourceMemoryAllows a (sign * kStep) DBig m σ then (1 : ℝ) else 0) /
          ((kCopy + ell).factorial : ℝ) ^ Fintype.card S ≤
            (B : ℝ) / (giantSignedSmallOmissionNumber S (kCopy + ell) ell : ℝ) := by
  filter_upwards [giantSignedSmallOmission_budget_eventually A ell hbc] with L hL
  intro S _ _ J _ P Q kCopy hP hQ hdis hsep a ha kStep hk sign hsign DBig m B hB hcount hstep hlabels hlower
  exact giantSignedSmallRareTransfer_source_bound hP hQ hdis hsep a ha kStep hk sign hsign DBig m B hB hstep
    (L ^ b) (L ^ c) hlabels (hL _ hcount) hlower

end
end ArtinMatthews
