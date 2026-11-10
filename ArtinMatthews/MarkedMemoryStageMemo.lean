module

public import ArtinMatthews.MarkedMemoryPrefixMemo
public import ArtinMatthews.MarkedMemoryStageBirthMass
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

/-! A literal birth update transforms the memo before an operation
into the memo through that operation. The absent addresses of the
current stage remain none, and no future value is read. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]
variable {P : J → Finset Nat.Primes} {M B n : ℕ}

omit [Fintype J] [DecidableEq J] in
theorem markedMemoryStageDraw_mem
    (e : I → MarkedMemoryPotentialAddress J M B n) (he : Function.Injective e) (i : I) :
    e i∈markedBirthDrawSet e := (markedBirthDrawEquiv e he i).2

theorem markedMemoryStageBirthValues_apply (stage : ℕ)
    (old : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes)
    (e : I → MarkedMemoryPotentialAddress J M B n) (he : Function.Injective e)
    (t : (i : I) → ↥(P (markedMemoryPotentialGroup (e i)))) (i : I) :
    markedMemoryStageBirthValues stage old e he t (e i)=some (t i).1 :=
  markedBirthDrawValues_apply (fun a => P (markedMemoryPotentialGroup a)) e he
    (markedMemoryStageBase stage old) t i

theorem markedMemoryStageBirthValues_outside (stage : ℕ)
    (old : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes)
    (e : I → MarkedMemoryPotentialAddress J M B n) (he : Function.Injective e)
    (t : (i : I) → ↥(P (markedMemoryPotentialGroup (e i))))
    (a : MarkedMemoryPotentialAddress J M B n) (ha : a∉markedBirthDrawSet e) :
    markedMemoryStageBirthValues stage old e he t a=markedMemoryStageBase stage old a := by
  simp only [markedMemoryStageBirthValues,markedConditionalBirthValues,dite_eq_right ha]

theorem markedMemoryStageBirthValues_memo (stage : ℕ)
    (v : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes)
    (e : I → MarkedMemoryPotentialAddress J M B n) (he : Function.Injective e)
    (t : (i : I) → ↥(P (markedMemoryPotentialGroup (e i))))
    (htime : ∀ i,markedMemoryPotentialChronologicalTime (e i)=stage)
    (hvalue : ∀ i,v (e i)=some (t i).1)
    (habsent : ∀ a,markedMemoryPotentialChronologicalTime a=stage →
      a∉markedBirthDrawSet e → v a=none) :
    markedMemoryStageBirthValues stage (markedMemoryPotentialMemo v stage) e he t=
      markedMemoryPotentialMemo v (stage+1) := by
  classical
  funext a
  by_cases hd : a∈markedBirthDrawSet e
  · obtain ⟨i,hi⟩ := (markedBirthDrawEquiv e he).surjective ⟨a,hd⟩
    have hai : e i=a := congrArg Subtype.val hi
    subst a
    rw [markedMemoryStageBirthValues_apply,markedMemoryPotentialMemo_prior v (by
      rw [htime i]
      exact Nat.lt_succ_self stage)]
    exact (hvalue i).symm
  · rw [markedMemoryStageBirthValues_outside stage _ e he t a hd]
    unfold markedMemoryStageBase
    by_cases ht : markedMemoryPotentialChronologicalTime a=stage
    · rw [ite_eq_left ht,markedMemoryPotentialMemo_prior v (by omega),habsent a ht hd]
    · rw [ite_eq_right ht]
      by_cases hl : markedMemoryPotentialChronologicalTime a<stage
      · rw [markedMemoryPotentialMemo_prior v hl,
          markedMemoryPotentialMemo_prior v (Nat.lt_succ_of_lt hl)]
      · rw [markedMemoryPotentialMemo_future v (by omega),
          markedMemoryPotentialMemo_future v (by omega)]

theorem markedMemoryStageBirthGate_of_memo_event (stage : ℕ)
    (v : MarkedMemoryPotentialAddress J M B n → Option Nat.Primes)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (hσ : MarkedBirthPermutationEvent v σ)
    (e : I → MarkedMemoryPotentialAddress J M B n) (he : Function.Injective e)
    (t : (i : I) → ↥(P (markedMemoryPotentialGroup (e i))))
    (hmemo : markedMemoryStageBirthValues stage (markedMemoryPotentialMemo v stage) e he t=
      markedMemoryPotentialMemo v (stage+1)) :
    markedMemoryStageBirthGate σ stage (markedMemoryPotentialMemo v stage) e he t := by
  intro a ha
  change markedMemoryStageBirthValues stage (markedMemoryPotentialMemo v stage) e he t a≠none ∧
    markedMemoryStageBirthValues stage (markedMemoryPotentialMemo v stage) e he t a=
      markedMemoryStageBirthValues stage (markedMemoryPotentialMemo v stage) e he t
        (markedMemoryPotentialPivot σ a)
  rw [hmemo]
  have ht := (Finset.mem_filter.mp ha).2
  have hp := markedMemoryPotentialEarlier_time (markedMemoryStageNonpivots_parent_earlier σ stage ha)
  rcases markedMemoryPotentialPivot_event σ v hσ (Finset.mem_filter.mp ha).1 with
    ⟨_,_,_,heq,hperformed⟩
  rw [markedMemoryPotentialMemo_prior v (by omega),markedMemoryPotentialMemo_prior v (by omega)]
  exact ⟨hperformed,heq⟩

end
end ArtinMatthews
