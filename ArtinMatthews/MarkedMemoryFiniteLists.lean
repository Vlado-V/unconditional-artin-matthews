module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
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

/-! Ordered distinct batches have a genuine finite encoding.  The
length is bounded by the cardinality of the identity type, while its
order remains part of the data. -/
namespace ArtinMatthews
noncomputable section

def MarkedMemoryFiniteList (A : Type*) [Fintype A] :=
  {d : (Σ k : Fin (Fintype.card A+1),Fin k.1 → A) // Function.Injective d.2}

instance {A : Type*} [Fintype A] : Fintype (MarkedMemoryFiniteList A) := by
  classical
  unfold MarkedMemoryFiniteList
  infer_instance

def markedMemoryFiniteList_toList {A : Type*} [Fintype A]
    (d : MarkedMemoryFiniteList A) : List A := List.ofFn d.1.2

theorem markedMemoryFiniteList_nodup {A : Type*} [Fintype A]
    (d : MarkedMemoryFiniteList A) : (markedMemoryFiniteList_toList d).Nodup :=
  List.nodup_ofFn_ofInjective d.2

def markedMemoryFiniteList_ofList {A : Type*} [Fintype A]
    (l : List A) (h : l.Nodup) : MarkedMemoryFiniteList A :=
  ⟨⟨⟨l.length,Nat.lt_succ_of_le h.length_le_card⟩,l.get⟩,h.injective_get⟩

@[simp] theorem markedMemoryFiniteList_toList_ofList {A : Type*} [Fintype A]
    (l : List A) (h : l.Nodup) :
    markedMemoryFiniteList_toList (markedMemoryFiniteList_ofList l h)=l := List.ofFn_get l

theorem markedMemoryFiniteList_toList_injective {A : Type*} [Fintype A] :
    Function.Injective (markedMemoryFiniteList_toList (A := A)) := by
  rintro ⟨⟨k,f⟩,hf⟩ ⟨⟨l,g⟩,hg⟩ h
  have he : k.1=l.1 := by
    simpa only [markedMemoryFiniteList_toList,List.length_ofFn] using congrArg List.length h
  have hkl : k=l := Fin.ext he
  cases hkl
  have hfg : f=g := List.ofFn_injective h
  cases hfg
  rfl

end
end ArtinMatthews
