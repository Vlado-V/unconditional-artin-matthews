module

public import ArtinMatthews.MarkedMemoryFiniteLists
public import ArtinMatthews.MarkedMemoryHistoryBirthPermutations
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Forgetting the order of a finite injective identity list has the
literal factorial enumeration fiber. No distinctness of numeric marks
is used. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

def markedMemoryFiniteListSet (l : MarkedMemoryFiniteList A) : Finset A :=
  markedMemoryBirthBatch ⟨l.1.2,l.2⟩

omit [DecidableEq A] in
theorem markedMemoryFiniteListSet_card (l : MarkedMemoryFiniteList A) :
    (markedMemoryFiniteListSet l).card = l.1.1.val := markedMemoryBirthBatch_card _

omit [DecidableEq A] in
theorem markedMemoryFiniteListSet_mem (l : MarkedMemoryFiniteList A) (a : A) :
    a ∈ markedMemoryFiniteListSet l ↔ a ∈ markedMemoryFiniteList_toList l := by
  simp only [markedMemoryFiniteListSet,markedMemoryBirthBatch,Finset.mem_map,Finset.mem_univ,
    true_and,markedMemoryFiniteList_toList,List.mem_ofFn]
  rfl

def markedMemoryFiniteListOfEmbedding {m : ℕ} (e : Fin m ↪ A) : MarkedMemoryFiniteList A :=
  ⟨⟨⟨m,Nat.lt_succ_of_le (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective)⟩,e⟩,e.injective⟩

omit [DecidableEq A] in
theorem markedMemoryFiniteListOfEmbedding_set {m : ℕ} (e : Fin m ↪ A) :
    markedMemoryFiniteListSet (markedMemoryFiniteListOfEmbedding e) = markedMemoryBirthBatch e := rfl

omit [DecidableEq A] in
theorem markedMemoryFiniteListOfEmbedding_recover (l : MarkedMemoryFiniteList A) :
    markedMemoryFiniteListOfEmbedding (⟨l.1.2,l.2⟩ : Fin l.1.1.val ↪ A) = l := by
  rcases l with ⟨⟨⟨m,hm⟩,f⟩,hf⟩
  rfl

omit [Fintype A] [DecidableEq A] in
theorem markedMemoryBirthBatch_castDomain {m k : ℕ} (h : m = k) (e : Fin m ↪ A) :
    markedMemoryBirthBatch ((Equiv.cast (congrArg Fin h.symm)).toEmbedding.trans e) =
      markedMemoryBirthBatch e := by
  cases h
  rfl

omit [DecidableEq A] in
theorem markedMemoryFiniteListOfEmbedding_castDomain {m k : ℕ} (h : m = k) (e : Fin m ↪ A) :
    markedMemoryFiniteListOfEmbedding ((Equiv.cast (congrArg Fin h.symm)).toEmbedding.trans e) =
      markedMemoryFiniteListOfEmbedding e := by
  cases h
  rfl

def markedMemoryFiniteListFiberEmbedding (S : Finset A) :
    {l : MarkedMemoryFiniteList A // markedMemoryFiniteListSet l = S} ≃
      {e : Fin S.card ↪ A // markedMemoryBirthBatch e = S} where
  toFun l := by
    have hk : l.1.1.1.val = S.card := (markedMemoryFiniteListSet_card l.1).symm.trans (congrArg Finset.card l.2)
    exact ⟨(Equiv.cast (congrArg Fin hk.symm)).toEmbedding.trans ⟨l.1.1.2,l.1.2⟩,
      (markedMemoryBirthBatch_castDomain hk _).trans l.2⟩
  invFun e := ⟨markedMemoryFiniteListOfEmbedding e.1,e.2⟩
  left_inv l := by
    apply Subtype.ext
    have hk : l.1.1.1.val = S.card := (markedMemoryFiniteListSet_card l.1).symm.trans (congrArg Finset.card l.2)
    exact (markedMemoryFiniteListOfEmbedding_castDomain hk _).trans
      (markedMemoryFiniteListOfEmbedding_recover l.1)
  right_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl

def markedMemoryFiniteListFiberEquiv (S : Finset A) :
    {l : MarkedMemoryFiniteList A // markedMemoryFiniteListSet l = S} ≃ Equiv.Perm (Fin S.card) :=
  (markedMemoryFiniteListFiberEmbedding S).trans
    ((Equiv.subtypeEquivRight (fun e => by
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩)).trans
      ((markedMemoryBirthFiberEquiv (⟨S,rfl⟩ : MarkedMemoryBirthSets A S.card)).trans
        (Equiv.equivCongr (Equiv.refl _) (Finset.equivFin S))))

theorem markedMemoryFiniteListFiber_card (S : Finset A) :
    Fintype.card {l : MarkedMemoryFiniteList A // markedMemoryFiniteListSet l = S} = S.card.factorial := by
  rw [Fintype.card_congr (markedMemoryFiniteListFiberEquiv S),Fintype.card_perm,Fintype.card_fin]

def markedMemoryFiniteListCanonical (S : Finset A) : MarkedMemoryFiniteList A :=
  ((markedMemoryFiniteListFiberEquiv S).symm (Equiv.refl _)).1

omit [DecidableEq A] in
theorem markedMemoryFiniteListCanonical_set (S : Finset A) :
    markedMemoryFiniteListSet (markedMemoryFiniteListCanonical S) = S :=
  ((markedMemoryFiniteListFiberEquiv S).symm (Equiv.refl _)).2

end
end ArtinMatthews
