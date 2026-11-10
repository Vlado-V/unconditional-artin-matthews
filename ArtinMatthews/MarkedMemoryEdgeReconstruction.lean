module

public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeLabels
public import ArtinMatthews.MarkedMinorArcRawEdgeChoices
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

/-! Reverse edge coordinates record whether the new active identity is
an old pending index or a genuinely fresh prime. The source-last survival
flag and both slot permutations remain explicit; no fresh draw is attached
to an old promotion. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

def markedMemoryRunPromotion (a : (j : J) → Fin (s.2.2.1.1 j : ℕ) ⊕ ↥(P j)) :
    MarkedRawEdgePromotions s.2.2 := fun j => Sum.elim some (fun _ => none) (a j)

def markedMemoryRunLastPrime (a : (j : J) → Fin (s.2.2.1.1 j : ℕ) ⊕ ↥(P j)) :
    (j : J) → ↥(P j) := fun j => Sum.elim (fun k => (s.2.2.2 j k).1) id (a j)

theorem markedMemoryRunLastPrime_promoted
    (a : (j : J) → Fin (s.2.2.1.1 j : ℕ) ⊕ ↥(P j)) (j : J) (k : Fin (s.2.2.1.1 j : ℕ))
    (hk : markedMemoryRunPromotion s a j = some k) :
    markedMemoryRunLastPrime s a j = (s.2.2.2 j k).1 := by
  cases ha : a j with
  | inl i =>
    have hik : i = k := by simpa only [markedMemoryRunPromotion, ha, Sum.elim_inl, Option.some.injEq] using hk
    subst i
    simp only [markedMemoryRunLastPrime, ha, Sum.elim_inl]
  | inr p => simp only [markedMemoryRunPromotion, ha, Sum.elim_inr, reduceCtorEq] at hk

structure MarkedMemoryEdgeRunData where
  target : Z
  sourceLastSurvives : J → Bool
  targetLastOrigin : (j : J) → Fin (s.2.2.1.1 j : ℕ) ⊕ ↥(P j)
  old_hits : ∀ j k, targetLastOrigin j = Sum.inl k →
    MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (s.2.2.2 j k)
  memory_bound : (∑ j, ((markedRawGhostSurvivors s.2.2
    (markedRawEdgePromotionDeletion (markedMemoryRunPromotion s targetLastOrigin)) j).card +
      (if sourceLastSurvives j then 1 else 0))) ≤ B

def markedMemoryEdgeRunReconstruct (d : MarkedMemoryEdgeRunData hZ s) : MarkedRawEdgeChoice hZ s where
  target := d.target
  store := d.sourceLastSurvives
  promotions := markedMemoryRunPromotion s d.targetLastOrigin
  fresh := (markedRawEdgeDegreeLabelsEquiv s.2.2 (markedMemoryRunPromotion s d.targetLastOrigin)).symm
    ⟨markedMemoryRunLastPrime s d.targetLastOrigin,markedMemoryRunLastPrime_promoted s d.targetLastOrigin⟩
  promotion_hits := by
    intro j k hk
    apply d.old_hits j k
    cases ha : d.targetLastOrigin j with
    | inl i =>
      have hik : i = k := by simpa only [markedMemoryRunPromotion, ha, Sum.elim_inl, Option.some.injEq] using hk
      exact congrArg Sum.inl hik
    | inr p => simp only [markedMemoryRunPromotion, ha, Sum.elim_inr, reduceCtorEq] at hk
  memory_bound := d.memory_bound

theorem markedMemoryEdgeRunReconstruct_last (d : MarkedMemoryEdgeRunData hZ s) :
    markedRawEdgeTargetLast s.2.2 (markedMemoryEdgeRunReconstruct hZ s d).promotions
        (markedMemoryEdgeRunReconstruct hZ s d).fresh = markedMemoryRunLastPrime s d.targetLastOrigin := by
  rw [← markedRawEdgeDegreeLabelsEquiv_value]
  exact congrArg Subtype.val ((markedRawEdgeDegreeLabelsEquiv s.2.2
    (markedMemoryRunPromotion s d.targetLastOrigin)).apply_symm_apply _)

def markedMemoryEdgeRunEncodeLast (c : MarkedRawEdgeChoice hZ s) (j : J) :
    Fin (s.2.2.1.1 j : ℕ) ⊕ ↥(P j) :=
  match c.promotions j with
  | none => Sum.inr (markedRawEdgeTargetLast s.2.2 c.promotions c.fresh j)
  | some k => Sum.inl k

theorem markedMemoryEdgeRunEncodeLast_promotion (c : MarkedRawEdgeChoice hZ s) :
    markedMemoryRunPromotion s (markedMemoryEdgeRunEncodeLast hZ s c) = c.promotions := by
  funext j
  unfold markedMemoryRunPromotion markedMemoryEdgeRunEncodeLast
  cases c.promotions j <;> rfl

theorem markedMemoryEdgeRunEncodeLast_prime (c : MarkedRawEdgeChoice hZ s) :
    markedMemoryRunLastPrime s (markedMemoryEdgeRunEncodeLast hZ s c) =
      markedRawEdgeTargetLast s.2.2 c.promotions c.fresh := by
  funext j
  unfold markedMemoryRunLastPrime markedMemoryEdgeRunEncodeLast
  split
  · rfl
  · rename_i k hk
    exact (markedRawEdgeTargetLast_promoted s.2.2 c.promotions c.fresh j k hk).symm

def markedMemoryEdgeRunEncode (c : MarkedRawEdgeChoice hZ s) : MarkedMemoryEdgeRunData hZ s where
  target := c.target
  sourceLastSurvives := c.store
  targetLastOrigin := markedMemoryEdgeRunEncodeLast hZ s c
  old_hits := by
    intro j k hk
    apply c.promotion_hits j k
    have hh : markedMemoryRunPromotion s (markedMemoryEdgeRunEncodeLast hZ s c) j = some k := by
      simp only [markedMemoryRunPromotion, hk, Sum.elim_inl]
    simpa only [markedMemoryEdgeRunEncodeLast_promotion] using hh
  memory_bound := by simpa only [markedMemoryEdgeRunEncodeLast_promotion] using c.memory_bound

@[ext] theorem MarkedMemoryEdgeRunData.ext {a b : MarkedMemoryEdgeRunData hZ s}
    (ht : a.target = b.target) (hs : a.sourceLastSurvives = b.sourceLastSurvives)
    (ho : a.targetLastOrigin = b.targetLastOrigin) : a = b := by
  cases a
  cases b
  cases ht
  cases hs
  cases ho
  rfl

theorem markedMemoryEdgeRun_encode_reconstruct (d : MarkedMemoryEdgeRunData hZ s) :
    markedMemoryEdgeRunEncode hZ s (markedMemoryEdgeRunReconstruct hZ s d) = d := by
  apply MarkedMemoryEdgeRunData.ext
  · rfl
  · rfl
  · funext j
    change markedMemoryEdgeRunEncodeLast hZ s (markedMemoryEdgeRunReconstruct hZ s d) j = _
    unfold markedMemoryEdgeRunEncodeLast
    change (match markedMemoryRunPromotion s d.targetLastOrigin j with
      | none => Sum.inr (markedRawEdgeTargetLast s.2.2 (markedMemoryEdgeRunReconstruct hZ s d).promotions
        (markedMemoryEdgeRunReconstruct hZ s d).fresh j)
      | some k => Sum.inl k) = d.targetLastOrigin j
    rw [markedMemoryEdgeRunReconstruct_last]
    cases ha : d.targetLastOrigin j <;> simp only [markedMemoryRunPromotion, markedMemoryRunLastPrime, ha, Sum.elim_inl, Sum.elim_inr, id_eq]

theorem markedMemoryEdgeRunEncode_injective : Function.Injective (markedMemoryEdgeRunEncode hZ s) := by
  intro a b hab
  have ht := congrArg MarkedMemoryEdgeRunData.target hab
  have hs := congrArg MarkedMemoryEdgeRunData.sourceLastSurvives hab
  have ho := congrArg MarkedMemoryEdgeRunData.targetLastOrigin hab
  have hp : a.promotions = b.promotions := by
    have h := congrArg (markedMemoryRunPromotion s) ho
    simpa only [markedMemoryEdgeRunEncode, markedMemoryEdgeRunEncodeLast_promotion] using h
  have hv : markedRawEdgeTargetLast s.2.2 a.promotions a.fresh =
      markedRawEdgeTargetLast s.2.2 b.promotions b.fresh := by
    have h := congrArg (markedMemoryRunLastPrime s) ho
    simpa only [markedMemoryEdgeRunEncode, markedMemoryEdgeRunEncodeLast_prime] using h
  apply markedRawEdgeChoiceCode_injective hZ s
  rcases a with ⟨ta,sa,pa,fa,hpa,hba⟩
  rcases b with ⟨tb,sb,pb,fb,hpb,hbb⟩
  dsimp only at ht hs hp hv
  cases ht
  cases hs
  cases hp
  have hf : fa = fb := by
    apply (markedRawEdgeDegreeLabelsEquiv s.2.2 pa).injective
    apply Subtype.ext
    simpa only [markedRawEdgeDegreeLabelsEquiv_value] using hv
  cases hf
  rfl

theorem markedMemoryEdgeRun_reconstruct_encode (c : MarkedRawEdgeChoice hZ s) :
    markedMemoryEdgeRunReconstruct hZ s (markedMemoryEdgeRunEncode hZ s c) = c := by
  apply markedMemoryEdgeRunEncode_injective hZ s
  exact markedMemoryEdgeRun_encode_reconstruct hZ s (markedMemoryEdgeRunEncode hZ s c)

def markedMemoryEdgeRunEquiv : MarkedRawEdgeChoice hZ s ≃ MarkedMemoryEdgeRunData hZ s where
  toFun := markedMemoryEdgeRunEncode hZ s
  invFun := markedMemoryEdgeRunReconstruct hZ s
  left_inv := markedMemoryEdgeRun_reconstruct_encode hZ s
  right_inv := markedMemoryEdgeRun_encode_reconstruct hZ s

end
end ArtinMatthews
