module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeIndices
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFresh
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

/-! Literal fixed-promotion-group coding into independent old indices,
fresh labels, target positions and store subsets. -/
noncomputable section
namespace ArtinMatthews

def markedDirtyFixedPromotionTuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (I : Finset J) (hI : markedDirtyEdgePromotedGroups prom=I) :
    MarkedRawPromotionTuple m I :=
  fun j => markedDirtyEdgePromotedIndex prom ⟨j.1,hI.symm ▸ j.2⟩

theorem markedDirtyFixedPromotionTuple_spec {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (I : Finset J) (hI : markedDirtyEdgePromotedGroups prom=I) (j : I) :
    prom j.1=some (markedDirtyFixedPromotionTuple m prom I hI j) :=
  markedDirtyEdgePromotedIndex_spec prom ⟨j.1,hI.symm ▸ j.2⟩

abbrev MarkedDirtyFixedEdgeChoice {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) :=
  {choice : MarkedRawEdgeChoice hZ s // markedDirtyEdgePromotedGroups choice.promotions=I}

def markedDirtyFixedEdgeChoiceCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (choice : MarkedDirtyFixedEdgeChoice hZ s I) :
    Z × ((J → Bool) × (MarkedRawPromotionTuple s.2.2 I × ((j : ↥(Finset.univ \ I)) → ↥(P j.1)))) :=
  (choice.1.target,(choice.1.store,(markedDirtyFixedPromotionTuple s.2.2 choice.1.promotions I choice.2,
    fun j => markedRawEdgeTargetLast s.2.2 choice.1.promotions choice.1.fresh j.1)))

theorem markedDirtyFixedEdgeChoiceCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) :
    Function.Injective (markedDirtyFixedEdgeChoiceCode hZ s I) := by
  classical
  rintro ⟨⟨ta,sa,pa,fa,hpa,hba⟩,hIa⟩ ⟨⟨tb,sb,pb,fb,hpb,hbb⟩,hIb⟩ he
  have ht := congrArg Prod.fst he
  have hs := congrArg (fun c => c.2.1) he
  have hi := congrArg (fun c => c.2.2.1) he
  have hf := congrArg (fun c => c.2.2.2) he
  have hp : pa=pb := by
    funext j
    by_cases hj : j ∈ I
    · have ha := markedDirtyFixedPromotionTuple_spec s.2.2 pa I hIa ⟨j,hj⟩
      have hb := markedDirtyFixedPromotionTuple_spec s.2.2 pb I hIb ⟨j,hj⟩
      rw [ha,hb]
      exact congrArg some (congrFun hi ⟨j,hj⟩)
    · have ha : pa j=none := by
        by_contra hn
        exact hj (hIa ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
      have hb : pb j=none := by
        by_contra hn
        exact hj (hIb ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
      rw [ha,hb]
  cases hp
  have hfab : fa=fb := by
    apply markedDirtyEdgeFreshTuple_injective s.2.2 pa
    funext j
    have hj : j.1 ∈ Finset.univ \ I := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro hin
      have hpnone := (Finset.mem_filter.mp j.2).2
      have hpne := (Finset.mem_filter.mp (hIa.symm ▸ hin)).2
      exact hpne hpnone
    exact congrFun hf ⟨j.1,hj⟩
  cases hfab
  cases ht
  cases hs
  rfl

end ArtinMatthews
