module

public import ArtinMatthews.MarkedMemoryActivePathData
public import ArtinMatthews.MarkedMemoryIndependentMarks
public import ArtinMatthews.MarkedMemoryIndependentBirths
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

/-! A birth-distinct independent reconstruction supplies its genuine
active prime path, including the physical incoming/source ban. The ban
is derived from the equal-size active exchange; it is not assumed as
part of a new path correspondence. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))

omit [∀ j,DecidableEq (A j)] in
def markedMemoryIndependentBandPrimeEmbedding (j : J) : A j ↪ ↥(P j) where
  toFun a := (d.particle j a).1
  inj' := by
    intro a b h
    have he := hinj (show markedMemoryIndependentPrime hZ d ⟨j,a⟩=
      markedMemoryIndependentPrime hZ d ⟨j,b⟩ from congrArg Subtype.val h)
    exact eq_of_heq (Sigma.mk.inj he).2

local notation "emb" => markedMemoryIndependentBandPrimeEmbedding hZ d hinj

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependentPrimePath_exchange (v : Fin n) (j : J) (p : P j) :
    (∃ k,emb j (d.activeId v.succ.val j k)=p) ↔
      ((∃ k,emb j (d.activeId v.castSucc.val j k)=p) ∧
        p≠emb j ((d.lifespan j).outgoing (2*v.val+1))) ∨
      p=emb j ((d.lifespan j).incoming (2*v.val+1)) := by
  have hout := markedMemoryIndependentOutgoing_eq hZ d v.val v.isLt j
  have hinc := markedMemoryIndependentIncoming_eq hZ d v.val v.isLt j
  have hex := markedMemoryIndependentActive_exchange hZ d v.val v.isLt j
  simp only [Fin.val_succ,Fin.val_castSucc]
  constructor
  · rintro ⟨k,hk⟩
    rcases (hex _).mp ⟨k,rfl⟩ with ⟨⟨l,hl⟩,hne⟩ | he
    · refine Or.inl ⟨⟨l,(congrArg (emb j) hl).trans hk⟩,?_⟩
      intro hp
      apply hne
      apply (emb j).injective
      exact hk.trans (hp.trans (congrArg (emb j) hout).symm)
    · exact Or.inr (hk.symm.trans (congrArg (emb j) (he.trans hinc)))
  · rintro (⟨⟨k,hk⟩,hne⟩ | hi)
    · have hn : d.activeId v.val j k≠d.activeId v.val j (markedMemoryIndependentOutgoing hZ d v.val v.isLt j) := by
        intro he
        apply hne
        exact hk.symm.trans (congrArg (emb j) (he.trans hout))
      obtain ⟨l,hl⟩ := (hex _).mpr (Or.inl ⟨⟨k,rfl⟩,hn⟩)
      exact ⟨l,(congrArg (emb j) hl).trans hk⟩
    · exact ⟨markedMemoryIndependentIncoming hZ d v.val v.isLt j,
        (congrArg (emb j) hinc).trans hi.symm⟩

def markedMemoryIndependentActivePath : MarkedMemoryActivePathData P pads Z n where
  position v := d.position v.val
  active v j := (d.activeId v.val j).trans (emb j)
  incoming v j := emb j ((d.lifespan j).incoming (2*v.val+1))
  outgoing v j := emb j ((d.lifespan j).outgoing (2*v.val+1))
  outgoing_present v j := (markedMemoryIndependentOutgoing_exists hZ d v.val v.isLt j).imp
    (fun k hk => congrArg (emb j) hk)
  incoming_present v j := (markedMemoryIndependentIncoming_exists hZ d v.val v.isLt j).imp
    (fun k hk => congrArg (emb j) hk)
  incoming_not_source := by
    intro v j h
    obtain ⟨k,hk⟩ := h
    have he := (emb j).injective hk
    apply markedMemoryIndependentIncoming_not_active hZ d v.val v.isLt j
    apply ((d.lifespan j).ghost_active (2*v.val) (by omega) (by omega) _).mpr
    exact (d.active_mem v.val (by omega) j _).mpr ⟨k,he⟩
  exchange := markedMemoryIndependentPrimePath_exchange hZ d hinj

end
end ArtinMatthews
