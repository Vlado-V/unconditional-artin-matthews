module

public import ArtinMatthews.MarkedMinorArcDirtyPromotionChoices
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

/-! Exact finite reindexings used by the actual delta edge row. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyPromotionTupleErase {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B} {I : Finset J}
    (t : MarkedRawPromotionTuple m I) (jstar : J) : MarkedRawPromotionTuple m (I.erase jstar) :=
  fun j => t ⟨j.1,(Finset.mem_erase.mp j.2).2⟩

def markedDirtyPromotionTupleSplit {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) (I : Finset J)
    (jstar : J) (hstar : jstar ∈ I) :
    MarkedRawPromotionTuple m I ≃ Fin (m.1.1 jstar:ℕ) × MarkedRawPromotionTuple m (I.erase jstar) where
  toFun t := (t ⟨jstar,hstar⟩,markedDirtyPromotionTupleErase t jstar)
  invFun t j := if h : j.1=jstar then h.symm ▸ t.1 else
    t.2 ⟨j.1,Finset.mem_erase.mpr ⟨h,j.2⟩⟩
  left_inv t := by
    funext j
    dsimp only
    split_ifs with h
    · cases h
      rfl
    · rfl
  right_inv t := by
    apply Prod.ext
    · simp
    · funext j
      have hn := (Finset.mem_erase.mp j.2).1
      simp only [markedDirtyPromotionTupleErase,dite_eq_right hn]

/-- Enlarging an actual finite injective image loses no index factor. -/
theorem markedDirtyFinite_sum_le_of_injective {α β : Type*} [Fintype α] [Fintype β]
    (e : α → β) (he : Function.Injective e) (f : α → ℝ) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b) (hfg : ∀ a, f a ≤ g (e a)) : (∑ a, f a) ≤ ∑ b, g b := by
  classical
  calc
    _ ≤ ∑ a, g (e a) := Finset.sum_le_sum (fun a _ => hfg a)
    _ = ∑ b ∈ Finset.univ.image e, g b :=
      (Finset.sum_image (fun _ _ _ _ h => he h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hg b)

end ArtinMatthews
