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
public import Mathlib.Tactic.Basify
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

/-! Actual promotion/fresh labels inject into independent finite group
patterns, indexed promotions, and fresh-only product coordinates. -/
noncomputable section
namespace ArtinMatthews

theorem markedDirtyEdgeFreshGroups_eq_compl {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) :
    markedDirtyEdgeFreshGroups prom=Finset.univ \ markedDirtyEdgePromotedGroups prom := by
  classical
  ext j
  simp only [markedDirtyEdgeFreshGroups,markedDirtyEdgePromotedGroups,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_sdiff,not_not]

def markedDirtyEdgeComplementFreshTuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) :
    (j : ↥(Finset.univ \ markedDirtyEdgePromotedGroups prom)) → ↥(P j.1) :=
  fun j => markedRawEdgeTargetLast m prom fresh j.1

theorem markedDirtyEdgeComplementFreshTuple_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) :
    Function.Injective (markedDirtyEdgeComplementFreshTuple m prom) := by
  intro a b hab
  apply markedDirtyEdgeFreshTuple_injective m prom
  funext j
  exact congrFun hab ⟨j.1,by rw [← markedDirtyEdgeFreshGroups_eq_compl]; exact j.2⟩

abbrev MarkedDirtyEdgeLabelCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) :=
  Σ code : (Σ I : Finset J, MarkedRawPromotionTuple m I), (j : ↥(Finset.univ \ code.1)) → ↥(P j.1)

def markedDirtyEdgeLabelCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (labels : Σ prom : MarkedRawEdgePromotions m, MarkedRawEdgeFreshLabels prom) : MarkedDirtyEdgeLabelCode m :=
  ⟨markedDirtyEdgePromotionCode labels.1,markedDirtyEdgeComplementFreshTuple m labels.1 labels.2⟩

theorem markedDirtyEdgeLabelCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) :
    Function.Injective (markedDirtyEdgeLabelCode m) := by
  rintro ⟨pa,fa⟩ ⟨pb,fb⟩ he
  have hc := congrArg Sigma.fst he
  change markedDirtyEdgePromotionCode pa=markedDirtyEdgePromotionCode pb at hc
  have hp := markedDirtyEdgePromotionCode_injective hc
  cases hp
  have hf : markedDirtyEdgeComplementFreshTuple m pa fa=markedDirtyEdgeComplementFreshTuple m pa fb :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have heq := markedDirtyEdgeComplementFreshTuple_injective m pa hf
  cases heq
  rfl

instance markedDirtyEdgeLabelCode_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) :
    Fintype (MarkedDirtyEdgeLabelCode m) := by
  classical
  unfold MarkedDirtyEdgeLabelCode
  infer_instance

/-- Full actual edge choice coding into ordinary product-law coordinates;
all admissibility restrictions are retained by the injective image. -/
def markedDirtyRawEdgeChoiceIndependentCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : Z × ((J → Bool) × MarkedDirtyEdgeLabelCode s.2.2) :=
  (choice.target,(choice.store,markedDirtyEdgeLabelCode s.2.2 ⟨choice.promotions,choice.fresh⟩))

theorem markedDirtyRawEdgeChoiceIndependentCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    Function.Injective (markedDirtyRawEdgeChoiceIndependentCode hZ s) := by
  intro a b hab
  have ht := congrArg Prod.fst hab
  have hh := congrArg Prod.snd hab
  have hs := congrArg Prod.fst hh
  have hlabels := congrArg Prod.snd hh
  apply markedRawEdgeChoiceCode_injective hZ s
  apply Prod.ext
  · exact ht
  · apply Prod.ext
    · exact hs
    · exact markedDirtyEdgeLabelCode_injective s.2.2 hlabels

end ArtinMatthews
