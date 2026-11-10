module

public import ArtinMatthews.GiantSignedRawEdgeData
public import ArtinMatthews.GiantSignedRawEdgeEnumeration
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

/-! The clean contribution is the literal zero-store and zero-promotion
part of the original raw edge choice sum. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantSignedEmptyEdgeChoice {B : Type*} {P : B → Finset ℕ} {t : B → ℕ}
    (m : GiantSignedMemory P) : GiantSignedEdgeChoice t m.1 :=
  ⟨fun _ => ∅, fun _ => ∅, fun _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩

def GiantSignedEdgeChoiceClean {B : Type*} {t n : B → ℕ}
    (c : GiantSignedEdgeChoice t n) : Prop :=
  c.1 = (fun _ => ∅) ∧ c.2.1 = (fun _ => ∅)

theorem giantSignedEdgeChoiceClean_iff {B : Type*} {P : B → Finset ℕ} {t : B → ℕ}
    (m : GiantSignedMemory P) (c : GiantSignedEdgeChoice t m.1) :
    GiantSignedEdgeChoiceClean c ↔ c = giantSignedEmptyEdgeChoice m := by
  constructor
  · rcases c with ⟨stores, promotions, e⟩
    rintro ⟨rfl,rfl⟩
    have he : e = (giantSignedEmptyEdgeChoice (t := t) m).2.2 := by
      funext g
      apply Function.Embedding.ext
      intro i
      exact Fin.elim0 i
    cases he
    rfl
  · rintro rfl
    exact ⟨rfl,rfl⟩

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedEdgeChoiceClean_sum {t : B → ℕ} (m : GiantSignedMemory PB)
    (F : GiantSignedEdgeChoice t m.1 → ℂ) :
    (∑ c : GiantSignedEdgeChoice t m.1, if GiantSignedEdgeChoiceClean c then F c else 0) =
      F (giantSignedEmptyEdgeChoice m) := by
  rw [Finset.sum_eq_single (giantSignedEmptyEdgeChoice m)]
  · exact ite_eq_left ((giantSignedEdgeChoiceClean_iff m _).mpr rfl)
  · intro c _ hc
    exact ite_eq_right (fun h => hc ((giantSignedEdgeChoiceClean_iff m c).mp h))
  · intro h
    exact (h (Finset.mem_univ _)).elim

def giantSignedRawCleanApply {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) : ℂ :=
  giantSignedRawEdgeApply ν V κ q ρ θ ζ K
    (fun _ r => if GiantSignedEdgeChoiceClean r.choice then 1 else 0) f s

theorem giantSignedRawCleanApply_expand {C : B → Finset (Fin k)}
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (q ρ θ ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient PB C ell)
    (f : GiantSignedState PS PB (k+ell) → ℂ) (s : GiantSignedState PS PB (k+ell)) :
    giantSignedRawCleanApply ν V κ q ρ θ ζ K f s =
      ∑ πS : S → Equiv.Perm (Fin (k+ell)), ∑ πB : B → Equiv.Perm (Fin (k+ell)),
      ∑ τS : S → Equiv.Perm (Fin (k+ell)), ∑ τB : B → Equiv.Perm (Fin (k+ell)),
      ∑ aux : GiantTwoSidedPatternAuxiliary PB C,
      ∑ tS : GiantTwoSidedResidueState PS (k+ell), ∑ tB : MarkedPhysicalMarking PB (k+ell),
        giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s
          ⟨πS,πB,τS,τB,aux,giantSignedEmptyEdgeChoice s.2.2,tS,tB⟩ *
          f (giantSignedRawEdgeTarget κ s
            ⟨πS,πB,τS,τB,aux,giantSignedEmptyEdgeChoice s.2.2,tS,tB⟩) := by
  classical
  unfold giantSignedRawCleanApply giantSignedRawEdgeApply
  rw [giantSignedRawEdgeMove_sum]
  dsimp only
  apply Finset.sum_congr (by ext; simp)
  intro πS _
  apply Finset.sum_congr (by ext; simp)
  intro πB _
  apply Finset.sum_congr (by ext; simp)
  intro τS _
  apply Finset.sum_congr (by ext; simp)
  intro τB _
  apply Finset.sum_congr (by ext; simp)
  intro aux _
  let F (c : GiantSignedEdgeChoice (fun g => ell + (C g).card) s.2.2.1) : ℂ :=
    ∑ tS : GiantTwoSidedResidueState PS (k+ell), ∑ tB : MarkedPhysicalMarking PB (k+ell),
      giantSignedRawEdgeCoefficient ν V κ q ρ θ ζ K s ⟨πS,πB,τS,τB,aux,c,tS,tB⟩ *
        f (giantSignedRawEdgeTarget κ s ⟨πS,πB,τS,τB,aux,c,tS,tB⟩)
  calc
    _ = ∑ c : GiantSignedEdgeChoice (fun g => ell + (C g).card) s.2.2.1,
        if GiantSignedEdgeChoiceClean c then F c else 0 := by
      apply Finset.sum_congr (by ext; simp)
      intro c _
      by_cases hc : GiantSignedEdgeChoiceClean c
      · simp only [hc, ite_true, mul_one, F]
        apply Finset.sum_congr (by ext; simp)
        intro tS _
        apply Finset.sum_congr (by ext; simp)
        intro tB _
        rfl
      · simp only [hc, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]
    _ = _ := giantSignedEdgeChoiceClean_sum s.2.2 F

end
end ArtinMatthews
