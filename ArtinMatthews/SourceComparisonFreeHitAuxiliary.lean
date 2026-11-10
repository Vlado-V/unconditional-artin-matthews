module

public import ArtinMatthews.SourceComparisonFreeHitUnion
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantTwoSidedPatternRunCompatibility
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

/-! The comparison displacement after removing the shared product is the
literal auxiliary product. Its prime divisors are represented by the
dependent performed slots, with their original multiplicities. -/

namespace ArtinMatthews
open Finset Set
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
  {C : J → Finset (Fin k)}

def sourceComparisonAuxiliaryHitRows (T : Finset ℕ) (aux : GiantTwoSidedPatternAuxiliary P C) :
    Finset ℕ :=
  sourceComparisonAuxHitRows T (Finset.univ : Finset (Σ j : J, ↥(C j)))
    (fun i => (aux i.1 i.2 : ℕ)) (giantTwoSidedPatternAuxiliaryProduct aux)

theorem mem_sourceComparisonAuxiliaryHitRows (hP : ∀ j p, p ∈ P j → p.Prime)
    (T : Finset ℕ) (aux : GiantTwoSidedPatternAuxiliary P C) (w : ℕ) :
    w ∈ sourceComparisonAuxiliaryHitRows T aux ↔
      w ∈ T ∧ ∃ p : ℕ, p.Prime ∧ p ∣ giantTwoSidedPatternAuxiliaryProduct aux ∧ p ∣ w := by
  rw [sourceComparisonAuxiliaryHitRows, mem_sourceComparisonAuxHitRows]
  constructor
  · rintro ⟨hw, ⟨j, i⟩, _, hh⟩
    have hp := hP j _ (aux j i).property
    have hd := (giantTwoSidedPatternAuxiliaryProduct_dvd_iff hP aux hp).2 ⟨j, i, rfl⟩
    have hh' : (aux j i : ℕ) ∣ w :=
      hh.elim id ((Nat.dvd_add_left hd).mp)
    exact ⟨hw, (aux j i : ℕ), hp, hd, hh'⟩
  · rintro ⟨hw, p, hp, hd, hwp⟩
    obtain ⟨j, i, hi⟩ := (giantTwoSidedPatternAuxiliaryProduct_dvd_iff hP aux hp).1 hd
    exact ⟨hw, ⟨j, i⟩, Finset.mem_univ _, Or.inl (by simpa only [hi] using hwp)⟩

theorem sourceComparisonAuxiliaryHitRows_of_common_prime (hP : ∀ j p, p ∈ P j → p.Prime)
    (aux : GiantTwoSidedPatternAuxiliary P C) {T : Finset ℕ} {w p : ℕ}
    (hw : w ∈ T) (hp : p.Prime) (hleft : p ∣ w)
    (hright : p ∣ w + giantTwoSidedPatternAuxiliaryProduct aux) :
    w ∈ sourceComparisonAuxiliaryHitRows T aux :=
  (mem_sourceComparisonAuxiliaryHitRows hP T aux w).2
    ⟨hw, p, hp, (Nat.dvd_add_right hleft).1 hright, hleft⟩

theorem sourceComparison_performed_auxiliary_lower {x : ℝ} (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (S : Finset (GiantCandidateGroupIndex x))
    (C : GiantCandidatePerformedBig S → Finset (Fin k))
    (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S C)) (g : S) (i : ↥(giantCandidatePerformedPattern S C g)) :
    Real.exp ((Real.log x) ^ (39 / 100 : ℝ)) ≤ ((aux g i : ℕ) : ℝ) := by
  rcases g with ⟨g | g, hg⟩
  · exact False.elim (Finset.notMem_empty _ i.property)
  · have hp : (aux ⟨Sum.inr g, hg⟩ i : ℕ) ∈ giantCandidateBigGroup x g :=
      (aux ⟨Sum.inr g, hg⟩ i).property
    exact (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hlog
      (by norm_num : (39 / 100 : ℝ) ≤ 40 / 100))).trans
      (giantCandidateBigGroup_range hx hlog hp).2.1

theorem sourceComparison_performed_freeHit_le {x : ℝ} (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (S : Finset (GiantCandidateGroupIndex x))
    (C : GiantCandidatePerformedBig S → Finset (Fin k))
    (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S C))
    (Ψ : ℝ → ℂ) (U V : ℕ → ℂ) {a b B : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ y ∉ Set.Icc a b, Ψ y = 0) (hB : ∀ y, ‖Ψ y‖ ≤ B) :
    let d := giantTwoSidedPatternAuxiliaryProduct aux
    let Y := x * (d : ℝ)
    ∀ (T : Finset ℕ), T ⊆ Finset.Ioc 0 ⌊b * Y⌋₊ →
      (∑ w ∈ sourceComparisonAuxiliaryHitRows T aux, sourceComparisonFreeHitWeight Ψ U V Y d w) ≤
        (B * Real.sqrt b / a) * Y ^ (-(1 / 2 : ℝ)) *
          (sourceComparisonFourthMass ⌊b * Y⌋₊ U) ^ (1 / 4 : ℝ) *
          (sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V) ^ (1 / 4 : ℝ) *
          ((Fintype.card (Σ g : S, ↥(giantCandidatePerformedPattern S C g)) : ℝ) *
            Real.exp (-(Real.log x) ^ (39 / 100 : ℝ) / 2)) := by
  dsimp only
  intro T hT
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let Y := x * (d : ℝ)
  let Q := Real.exp ((Real.log x) ^ (39 / 100 : ℝ))
  let I := (Finset.univ : Finset (Σ g : S, ↥(giantCandidatePerformedPattern S C g)))
  let p (i : Σ g : S, ↥(giantCandidatePerformedPattern S C g)) := (aux i.1 i.2 : ℕ)
  have hP (g : S) (p : ℕ) (hp : p ∈ giantCandidateGroup x g.val) : p.Prime :=
    (giantCandidateFullPrimes_range hx hlog (mem_giantCandidateFullPrimes.mpr ⟨g.val, hp⟩)).1
  have hd : 0 < d := by
    unfold d giantTwoSidedPatternAuxiliaryProduct
    exact Finset.prod_pos fun g _ =>
      Finset.prod_pos fun i _ => (hP g _ (aux g i).property).pos
  have hY : 0 < Y := mul_pos (zero_lt_one.trans hx) (by exact_mod_cast hd)
  have hdiv (i : Σ g : S, ↥(giantCandidatePerformedPattern S C g)) : p i ∣ d :=
    (giantTwoSidedPatternAuxiliaryProduct_dvd_iff hP aux (hP i.1 _ (aux i.1 i.2).property)).2
      ⟨i.1, i.2, rfl⟩
  have hh := sourceComparison_freeHit_union_le_of_lower Ψ U V hY ha hb hΨ hB d I p
    (show 0 < Q from Real.exp_pos _) (fun i _ => sourceComparison_performed_auxiliary_lower hx hlog S C aux i.1 i.2)
    (fun i _ => hdiv i) hT
  have hQ : Q ^ (-(1 / 2 : ℝ)) = Real.exp (-(Real.log x) ^ (39 / 100 : ℝ) / 2) := by
    dsimp only [Q]
    rw [← Real.exp_mul]
    congr 1
    ring
  change (∑ w ∈ sourceComparisonAuxHitRows T I p d, sourceComparisonFreeHitWeight Ψ U V Y d w) ≤ _
  simpa only [I, Finset.card_univ, hQ] using hh

end
end ArtinMatthews
