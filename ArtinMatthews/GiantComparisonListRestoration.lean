module

public import ArtinMatthews.GiantComparisonSeparatedSum
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

/-! Restoring both independent free lists leaves the copied bad mass
and the quotient rows hit by an auxiliary prime. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
  {k ell : ℕ} {C : J → Finset (Fin k)}

def GiantComparisonAuxiliaryHits (aux : GiantTwoSidedPatternAuxiliary P C) (w w' : ℕ) : Prop :=
  ∃ (g : J) (i : ↥(C g)), (aux g i : ℕ) ∣ w ∨ (aux g i : ℕ) ∣ w'

theorem giantComparisonUnsharedAuxAvoids_of_no_hit
    (aux : GiantTwoSidedPatternAuxiliary P C) {w w' : ℕ}
    (b : GiantComparisonFreeMarking P C ell w) (b' : GiantComparisonFreeMarking P C ell w')
    (h : ¬ GiantComparisonAuxiliaryHits aux w w') :
    GiantComparisonUnsharedAuxAvoids aux b.val b'.val := by
  intro g j i l
  constructor
  · intro he
    exact h ⟨g,i,Or.inl (he.symm ▸ b.property.2 j l)⟩
  · intro he
    exact h ⟨g,i,Or.inr (he.symm ▸ b'.property.2 j l)⟩

def giantComparisonRestorationLoss (aux : GiantTwoSidedPatternAuxiliary P C)
    (q : ℝ) (w w' : ℕ) : ℝ :=
  ((q⁻¹)^(2*(k*Fintype.card J))+1)*giantComparisonSharedBadMass aux w w' +
    if GiantComparisonAuxiliaryHits aux w w' then 1 else 0

theorem giantComparisonRestoredPair_error
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (L : GiantComparisonListCoefficient P C ell) (aux : GiantTwoSidedPatternAuxiliary P C)
    (w w' : ℕ) {q M : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hM : 0 ≤ M)
    (hL : ∀ b b', ‖L b b' aux‖ ≤ M) :
    ‖giantComparisonRestoredPair L aux q w w' - giantComparisonIndependentPair L aux q w w'‖ ≤
      M*giantComparisonRestorationLoss aux q w w'*
        giantComparisonIndependentDamping P C ell q w w' *
        (Fintype.card (GiantComparisonFreeMarking P C ell w):ℝ)*
        (Fintype.card (GiantComparisonFreeMarking P C ell w'):ℝ) := by
  let B := giantComparisonIndependentDamping P C ell q w w'
  let A := giantComparisonRestorationLoss aux q w w'
  let S := GiantComparisonFreeMarking P C ell w
  let T := GiantComparisonFreeMarking P C ell w'
  let δ (b : S) (b' : T) : ℂ :=
    L b.val b'.val aux*(giantComparisonRestoredSharedDamping aux q w w' b.val b'.val:ℂ) -
      (B:ℂ)*L b.val b'.val aux
  have hB : 0 ≤ B := by unfold B giantComparisonIndependentDamping giantComparisonQuotientDamping; positivity
  have hb (b : S) (b' : T) : ‖δ b b'‖ ≤ M*A*B := by
    have he := giantComparisonRestoredSharedDamping_error hP hdis hV aux b b' hq hq1
    have hI : (if GiantComparisonUnsharedAuxAvoids aux b.val b'.val then 0 else (1:ℝ)) ≤
        (if GiantComparisonAuxiliaryHits aux w w' then 1 else 0) := by
      by_cases hh : GiantComparisonAuxiliaryHits aux w w'
      · rw [ite_eq_left hh]
        split_ifs <;> norm_num
      · rw [ite_eq_right hh,ite_eq_left (giantComparisonUnsharedAuxAvoids_of_no_hit aux b b' hh)]
    have htail : ‖giantComparisonRestoredSharedDamping aux q w w' b.val b'.val-B‖ ≤ A*B :=
      he.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hI) hB)
    unfold δ
    rw [mul_comm (B:ℂ),← mul_sub,← Complex.ofReal_sub,norm_mul,Complex.norm_real,mul_assoc]
    exact mul_le_mul (hL b.val b'.val) htail (norm_nonneg _) hM
  rw [giantComparisonRestoredPair,giantComparisonIndependentPair]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  change ‖∑ b : S, ∑ b' : T, δ b b'‖ ≤ M*A*B*(Fintype.card S:ℝ)*(Fintype.card T:ℝ)
  calc
    _ ≤ ∑ b : S, ‖∑ b' : T, δ b b'‖ := norm_sum_le _ _
    _ ≤ ∑ b : S, ∑ b' : T, ‖δ b b'‖ := sum_le_sum fun b _ => norm_sum_le _ _
    _ ≤ ∑ _b : S, ∑ _b' : T, M*A*B := sum_le_sum fun b _ => sum_le_sum fun b' _ => hb b b'
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring

end
end ArtinMatthews
