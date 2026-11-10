module

public import ArtinMatthews.MarkedMemoryPrimeLifespanSupport
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

/-! Actual half-step endpoints of one compatible primewise lifespan.
These are the finite first/last coordinates used to construct the
independent memory family; no interval-support premise is inserted. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ}

def MarkedMemoryPrimeLifespanUsed (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) : Prop := A.Nonempty ∨ c≠(none,none)

def markedMemoryPrimeFirst (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N) : ℕ :=
  match c.1 with
  | some a => 2*a.val+1
  | none => if hA : A.Nonempty then 2*(A.min' hA).val else 0

def markedMemoryPrimeLast (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N) : ℕ :=
  match c.2 with
  | some b => 2*b.val
  | none => if hA : A.Nonempty then 2*(A.max' hA).val+1 else 0

theorem markedMemoryPrimeLast_bound (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N) :
    markedMemoryPrimeLast A c≤2*N+1 := by
  cases hb : c.2 with
  | none =>
    by_cases hA : A.Nonempty
    · simp only [markedMemoryPrimeLast,hb,dite_eq_left hA]
      have h := (A.max' hA).isLt
      omega
    · simp only [markedMemoryPrimeLast,hb,dite_eq_right hA]
      omega
  | some b =>
    simp only [markedMemoryPrimeLast,hb]
    have h := b.isLt
    omega

variable {L : Type*} (line : Fin (N+1) → L)
  (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N)

theorem markedMemoryPrimeFirst_active
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1)) (hv : v∈A) :
    markedMemoryPrimeFirst A c≤2*v.val := by
  have hA : A.Nonempty := ⟨v,hv⟩
  rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc
  have hm := A.min'_le v hv
  cases ha : c.1 with
  | none => simpa only [markedMemoryPrimeFirst,ha,dite_eq_left hA] using Nat.mul_le_mul_left 2 (show (A.min' hA).val≤v.val from hm)
  | some a =>
    have hab := (hc.2.1 a ha).1
    simp only [markedMemoryPrimeFirst,ha]
    omega

theorem markedMemoryPrimeLast_active
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1)) (hv : v∈A) :
    2*v.val+1 ≤ markedMemoryPrimeLast A c := by
  have hA : A.Nonempty := ⟨v,hv⟩
  rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc
  have hm := A.le_max' v hv
  cases hb : c.2 with
  | none =>
    simp only [markedMemoryPrimeLast,hb,dite_eq_left hA]
    omega
  | some b =>
    have hab := (hc.2.2 b hb).1
    simp only [markedMemoryPrimeLast,hb]
    omega

theorem markedMemoryPrimeLifespan_nonempty
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (hu : MarkedMemoryPrimeLifespanUsed A c) :
    markedMemoryPrimeFirst A c ≤ markedMemoryPrimeLast A c := by
  by_cases hA : A.Nonempty
  · have h₁ := markedMemoryPrimeFirst_active line A c hc (A.min' hA) (A.min'_mem hA)
    have h₂ := markedMemoryPrimeLast_active line A c hc (A.min' hA) (A.min'_mem hA)
    omega
  · rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hA] at hc
    rcases hc with hc | ⟨a,b,rfl,hab,_⟩
    · exact False.elim ((hu.resolve_left hA) hc)
    · simp only [markedMemoryPrimeFirst,markedMemoryPrimeLast]
      omega

theorem markedMemoryPrimeFirst_even_birth
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (hu : MarkedMemoryPrimeLifespanUsed A c) (v : Fin N)
    (hf : markedMemoryPrimeFirst A c=2*v.val+2) :
    v.succ∈A ∧ v.castSucc∉A := by
  have hA : A.Nonempty := by
    by_contra hA
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hA] at hc
    rcases hc with hc | ⟨a,b,rfl,_,_⟩
    · exact (hu.resolve_left hA) hc
    · simp only [markedMemoryPrimeFirst] at hf
      omega
  have hvs : v.succ.val=v.val+1 := rfl
  have hvc : v.castSucc.val=v.val := rfl
  cases ha : c.1 with
  | some a => simp only [markedMemoryPrimeFirst,ha] at hf; omega
  | none =>
    simp only [markedMemoryPrimeFirst,ha,dite_eq_left hA] at hf
    have he : A.min' hA=v.succ := Fin.ext (by omega)
    refine ⟨he ▸ A.min'_mem hA,?_⟩
    intro hv
    have hm := A.min'_le v.castSucc hv
    omega

theorem markedMemoryPrimeLast_odd_death
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (hu : MarkedMemoryPrimeLifespanUsed A c) (v : Fin N)
    (hl : markedMemoryPrimeLast A c=2*v.val+1) :
    v.castSucc∈A ∧ v.succ∉A := by
  have hA : A.Nonempty := by
    by_contra hA
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hA] at hc
    rcases hc with hc | ⟨a,b,rfl,_,_⟩
    · exact (hu.resolve_left hA) hc
    · simp only [markedMemoryPrimeLast] at hl
      omega
  have hvs : v.succ.val=v.val+1 := rfl
  have hvc : v.castSucc.val=v.val := rfl
  cases hb : c.2 with
  | some b => simp only [markedMemoryPrimeLast,hb] at hl; omega
  | none =>
    simp only [markedMemoryPrimeLast,hb,dite_eq_left hA] at hl
    have he : A.max' hA=v.castSucc := Fin.ext (by omega)
    refine ⟨he ▸ A.max'_mem hA,?_⟩
    intro hv
    have hm := A.le_max' v.succ hv
    omega

end
end ArtinMatthews
