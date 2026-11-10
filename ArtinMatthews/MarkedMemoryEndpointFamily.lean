module

public import ArtinMatthews.MarkedMemoryEndpointLaws
public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex
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

/-! A bare finite endpoint family is checked through its canonical birth
enumeration. All other birth enumerations are constructed and proved
admissible; no history or reindexing bijection is part of the data. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

structure MarkedMemoryEndpointConditions (d : MarkedMemoryEndpointData A P pads Z n) : Prop where
  laws : MarkedMemoryFiniteTableauLaws hZ B (markedMemoryEndpointCanonicalData d)
  source : markedMemoryIndependentState hZ
    (markedMemoryFiniteTableau_toIndependent hZ ⟨markedMemoryEndpointCanonicalData d,laws⟩) 0 (Nat.zero_le n)=s
  normalized : markedMemoryFiniteAnchorNormalize hZ (markedMemoryEndpointCanonicalData d)=
    markedMemoryEndpointCanonicalData d

def MarkedMemoryEndpointFamily :=
  {d : MarkedMemoryEndpointData A P pads Z n // MarkedMemoryEndpointConditions hZ s d}

instance markedMemoryEndpointFamily_fintype :
    Fintype (MarkedMemoryEndpointFamily (A := A) (n := n) hZ s) := by
  classical
  unfold MarkedMemoryEndpointFamily
  infer_instance

def markedMemoryEndpointFamilyTableau
    (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s) (births : MarkedMemoryEndpointBirthOrders e.1) :
    MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n :=
  ⟨markedMemoryEndpointDataDecorated e.1 births,
    markedMemoryEndpointLaws_transfer hZ e.1 (markedMemoryEndpointCanonicalBirths e.1) births e.2.laws⟩

omit [DecidableEq J] in
theorem markedMemoryEndpointFamilyTableau_source
    (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s) (births : MarkedMemoryEndpointBirthOrders e.1) :
    markedMemoryIndependentState hZ (markedMemoryFiniteTableau_toIndependent hZ
      (markedMemoryEndpointFamilyTableau hZ s e births)) 0 (Nat.zero_le n)=s :=
  e.2.source

def markedMemoryEndpointFamilyIndex
    (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s) (births : MarkedMemoryEndpointBirthOrders e.1)
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s :=
  ⟨⟨⟨markedMemoryEndpointFamilyTableau hZ s e births,
      markedMemoryEndpointFamilyTableau_source hZ s e births⟩,order⟩,
    (markedMemoryEndpointNormalize_iff hZ e.1 (markedMemoryEndpointCanonicalBirths e.1) births).mp e.2.normalized⟩

omit [DecidableEq J] in
theorem markedMemoryFiniteTableau_initial_empty
    (f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (hs : markedMemoryIndependentState hZ (markedMemoryFiniteTableau_toIndependent hZ f) 0 (Nat.zero_le n)=s)
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0) (j : J) :
    markedMemoryFiniteList_toList (f.1.initial j)=[] := by
  have hh := congrArg (fun u : MarkedRawState P (pads+1) B Z => (u.2.2.1.1 j:ℕ)) hs
  change (markedMemoryFiniteList_toList (f.1.initial j)).length=(s.2.2.1.1 j:ℕ) at hh
  exact List.eq_nil_of_length_eq_zero (hh.trans (hempty j))

def markedMemoryEndpointFamilyOfIndex
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s) :
    MarkedMemoryEndpointFamily (A := A) (n := n) hZ s := by
  let f := i.1.1.1
  let d := markedMemoryEndpointOfData f.1
  let births := markedMemoryEndpointOriginalBirths hZ f
  have hr := markedMemoryEndpointOriginal_rebuild hZ f
    (fun j => markedMemoryFiniteTableau_initial_empty hZ s f i.1.1.2 hempty j)
  have hl : MarkedMemoryFiniteTableauLaws hZ B (markedMemoryEndpointDataDecorated d births) := by
    rw [hr]
    exact f.2
  refine ⟨d,⟨markedMemoryEndpointLaws_transfer hZ d births (markedMemoryEndpointCanonicalBirths d) hl,?_,?_⟩⟩
  · have he : (⟨markedMemoryEndpointDataDecorated d births,hl⟩ : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n)=f := Subtype.ext hr
    have hs := i.1.1.2
    change markedMemoryIndependentState hZ (markedMemoryFiniteTableau_toIndependent hZ f) 0 (Nat.zero_le n)=s at hs
    rw [← he] at hs
    exact hs
  · apply (markedMemoryEndpointNormalize_iff hZ d births (markedMemoryEndpointCanonicalBirths d)).mp
    rw [hr]
    exact i.2

end
end ArtinMatthews
