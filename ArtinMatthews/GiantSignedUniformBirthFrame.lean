module

public import ArtinMatthews.GiantSignedBirthAddresses
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

/-! One common potential-address frame for all patterns. Its size H
limits only the displayed ghost addresses. The original dynamics and
their arbitrary finite memory degrees are unchanged. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev GiantSignedUniformBirthAddress (B : Type*) (M n H : ℕ) :=
  (B × Fin M) ⊕
    ((Σ _i : Fin n, Σ _g : B, Fin M) ⊕
      (Σ _i : Fin (n+1), Σ _g : B, Fin H))

def giantSignedFreeSlotEmbedding {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    Fin (ell + C.card) ↪ Fin (k+ell) where
  toFun i := giantTwoSidedPatternFreeSlot C ell (giantSignedPatternFreeSlotEquiv C ell i)
  inj' := by
    have hm : Function.Injective (Sum.map (Subtype.val : ↥C → Fin k) (id : Fin ell → Fin ell)) :=
      Sum.map_injective.mpr ⟨Subtype.val_injective, Function.injective_id⟩
    have he (s : GiantTwoSidedPatternFreeSlots C ell) :
        finSumFinEquiv (Sum.map (Subtype.val : ↥C → Fin k) (id : Fin ell → Fin ell) s) =
          giantTwoSidedPatternFreeSlot C ell s := by
      cases s with
      | inl i => exact finSumFinEquiv_apply_left i.val
      | inr i => exact finSumFinEquiv_apply_right i
    intro a b hab
    apply (giantSignedPatternFreeSlotEquiv C ell).injective
    apply hm
    apply finSumFinEquiv.injective
    simpa only [he] using hab

variable {B : Type*} {P : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedUniformBirthEmbedding (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) :
    GiantSignedPerformedBirth d ↪ GiantSignedUniformBirthAddress B (k+ell) n H where
  toFun := Sum.map id (Sum.map
    (Sigma.map id (fun i => Sigma.map id
      (fun g a => giantSignedFreeSlotEmbedding (C i g) ell a.val)))
    (Sigma.map id (fun i => Sigma.map id
      (fun g a => (⟨a.val, a.isLt.trans_le (hH i g)⟩ : Fin H)))))
  inj' := by
    apply Sum.map_injective.mpr
    refine ⟨Function.injective_id, ?_⟩
    apply Sum.map_injective.mpr
    constructor
    · apply Function.injective_id.sigma_map
      intro i
      apply Function.injective_id.sigma_map
      intro g
      exact (giantSignedFreeSlotEmbedding (C i g) ell).injective.comp Subtype.val_injective
    · apply Function.injective_id.sigma_map
      intro i
      apply Function.injective_id.sigma_map
      intro g a b hab
      exact Fin.ext (congrArg (fun s : Fin H => s.val) hab)

def giantSignedUniformBirthValue (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) (a : GiantSignedUniformBirthAddress B (k+ell) n H) : Option ℕ :=
  if h : ∃ b, giantSignedUniformBirthEmbedding d H hH b = a then
    some (giantSignedPerformedBirthPrime d (Classical.choose h))
  else none

theorem giantSignedUniformBirthValue_embedding (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) (b : GiantSignedPerformedBirth d) :
    giantSignedUniformBirthValue d H hH (giantSignedUniformBirthEmbedding d H hH b) =
      some (giantSignedPerformedBirthPrime d b) := by
  have hx : ∃ a, giantSignedUniformBirthEmbedding d H hH a =
      giantSignedUniformBirthEmbedding d H hH b := ⟨b, rfl⟩
  rw [giantSignedUniformBirthValue, dite_eq_left hx]
  have he : Classical.choose hx = b :=
    (giantSignedUniformBirthEmbedding d H hH).injective (Classical.choose_spec hx)
  rw [he]

theorem giantSignedUniformBirthValue_initial (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) (g : B) (s : Fin (k+ell)) :
    giantSignedUniformBirthValue d H hH (.inl ⟨g,s⟩) = some (d.initial g s).val :=
  giantSignedUniformBirthValue_embedding d H hH (.inl ⟨g,s⟩)

theorem giantSignedUniformBirthValue_fresh (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) (i : Fin n) (g : B)
    (s : Fin (ell + (C i g).card)) (hs : s ∉ d.promoted i g) :
    giantSignedUniformBirthValue d H hH
      (.inr (.inl ⟨i,g,giantSignedFreeSlotEmbedding (C i g) ell s⟩)) =
        some (giantSignedPatternFreeLabels (C i) (d.target i) g s).val :=
  giantSignedUniformBirthValue_embedding d H hH (.inr (.inl ⟨i,g,⟨s,hs⟩⟩))

theorem giantSignedUniformBirthValue_ghost (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) (i : Fin (n+1)) (g : B) (s : Fin (batch i g)) :
    giantSignedUniformBirthValue d H hH
      (.inr (.inr ⟨i,g,⟨s.val,s.isLt.trans_le (hH i g)⟩⟩)) = some (d.born i g s).val :=
  giantSignedUniformBirthValue_embedding d H hH (.inr (.inr ⟨i,g,s⟩))

theorem giantSignedUniformBirthValue_unperformed (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) (a : GiantSignedUniformBirthAddress B (k+ell) n H)
    (ha : ¬ ∃ b, giantSignedUniformBirthEmbedding d H hH b = a) :
    giantSignedUniformBirthValue d H hH a = none :=
  dite_eq_right ha

theorem giantSignedUniformBirthValue_covers (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) (a : GiantSignedUniformBirthAddress B (k+ell) n H)
    (ha : giantSignedUniformBirthValue d H hH a ≠ none) :
    ∃ b, giantSignedUniformBirthEmbedding d H hH b = a := by
  by_contra hn
  exact ha (dite_eq_right hn)

theorem giantSignedBirthDistinct_iff_uniform (d : GiantSignedBirthData P ell C batch) (H : ℕ)
    (hH : ∀ i g, batch i g ≤ H) :
    GiantSignedBirthDistinct d ↔ MarkedPerformedInjective (giantSignedUniformBirthValue d H hH) := by
  constructor
  · intro hd a ha b hb hab
    obtain ⟨a', rfl⟩ := giantSignedUniformBirthValue_covers d H hH a ha
    obtain ⟨b', rfl⟩ := giantSignedUniformBirthValue_covers d H hH b hb
    rw [giantSignedUniformBirthValue_embedding, giantSignedUniformBirthValue_embedding] at hab
    exact congrArg (giantSignedUniformBirthEmbedding d H hH) (hd (Option.some.inj hab))
  · intro hd a b hab
    apply (giantSignedUniformBirthEmbedding d H hH).injective
    apply hd
    · change giantSignedUniformBirthValue d H hH (giantSignedUniformBirthEmbedding d H hH a) ≠ none
      rw [giantSignedUniformBirthValue_embedding]
      exact Option.some_ne_none _
    · change giantSignedUniformBirthValue d H hH (giantSignedUniformBirthEmbedding d H hH b) ≠ none
      rw [giantSignedUniformBirthValue_embedding]
      exact Option.some_ne_none _
    · rw [giantSignedUniformBirthValue_embedding, giantSignedUniformBirthValue_embedding, hab]

theorem giantSignedUniformBirthAddress_card [Fintype B] (M N H : ℕ) :
    Fintype.card (GiantSignedUniformBirthAddress B M N H) =
      (N+1) * Fintype.card B * (M+H) := by
  simp only [GiantSignedUniformBirthAddress, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_sigma, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id]
  ring

end
end ArtinMatthews
