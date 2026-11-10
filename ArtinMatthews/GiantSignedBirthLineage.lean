module

public import ArtinMatthews.GiantSignedChronologicalOrigins
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

/-! Every live index inherits an actual birth. A transition can combine
old and new origins because their chronological times are disjoint. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] {PS : S → Finset ℕ} {PB : B → Finset ℕ}
    {k ell n M : ℕ} {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedPerformedBirthTime (d : GiantSignedBirthData PB ell C batch) :
    GiantSignedPerformedBirth d → ℕ
  | .inl _ => 0
  | .inr (.inl a) => 2*a.1.val + 2
  | .inr (.inr a) => 2*a.1.val + 1

structure GiantSignedBirthLineage (d : GiantSignedBirthData PB ell C batch)
    (s : GiantSignedState PS PB M) (g : B) (t : ℕ) where
  origin : GiantSignedStateLiveSlots s g ↪ GiantSignedPerformedBirth d
  time_le : ∀ i, giantSignedPerformedBirthTime d (origin i) ≤ t
  prime_eq : ∀ i, giantSignedPerformedBirthPrime d (origin i) = (giantSignedStateLivePrime s g i).val

private def giantSignedLineageSumEmbedding {X Y A : Type*} (clock : A → ℕ)
    (e : X ↪ A) (f : Y ↪ A) (t : ℕ) (he : ∀ x, clock (e x) ≤ t)
    (hf : ∀ y, t < clock (f y)) : X ⊕ Y ↪ A where
  toFun := Sum.elim e f
  inj' := by
    rintro (x | y) (x' | y') h
    · exact congrArg Sum.inl (e.injective h)
    · change e x = f y' at h
      exact False.elim (not_lt_of_ge (he x) (h.symm ▸ hf y'))
    · change f y = e x' at h
      exact False.elim (not_lt_of_ge (he x') (h ▸ hf y))
    · exact congrArg Sum.inr (f.injective h)

def giantSignedBirthLineage_extend {X : Type*} {d : GiantSignedBirthData PB ell C batch}
    {s u : GiantSignedState PS PB M} {g : B} {t t' : ℕ} (l : GiantSignedBirthLineage d s g t)
    (e : GiantSignedStateLiveSlots u g ↪ (GiantSignedStateLiveSlots s g ⊕ X))
    (fresh : X ↪ GiantSignedPerformedBirth d) (hle : t ≤ t')
    (hfresh : ∀ i, t < giantSignedPerformedBirthTime d (fresh i))
    (hclock : ∀ i, giantSignedPerformedBirthTime d (fresh i) ≤ t')
    (hvalue : ∀ i, (giantSignedStateLivePrime u g i).val =
      Sum.elim (fun z => (giantSignedStateLivePrime s g z).val)
        (fun z => giantSignedPerformedBirthPrime d (fresh z)) (e i)) :
    GiantSignedBirthLineage d u g t' where
  origin := e.trans (giantSignedLineageSumEmbedding (giantSignedPerformedBirthTime d)
    l.origin fresh t l.time_le hfresh)
  time_le i := by
    change giantSignedPerformedBirthTime d (Sum.elim l.origin fresh (e i)) ≤ t'
    rcases e i with z | z
    · exact (l.time_le z).trans hle
    · exact hclock z
  prime_eq i := by
    change giantSignedPerformedBirthPrime d (Sum.elim l.origin fresh (e i)) = _
    rw [hvalue i]
    rcases e i with z | z
    · exact l.prime_eq z
    · rfl

theorem giantSignedBirthLineage_injective {d : GiantSignedBirthData PB ell C batch}
    {s : GiantSignedState PS PB M} {g : B} {t : ℕ} (l : GiantSignedBirthLineage d s g t)
    (hd : GiantSignedBirthDistinct d) : Function.Injective (giantSignedStateLivePrime s g) := by
  intro i j hij
  apply l.origin.injective
  apply hd
  rw [l.prime_eq, l.prime_eq, hij]

theorem giantSignedBirthLineage_card_le {d : GiantSignedBirthData PB ell C batch}
    {s : GiantSignedState PS PB M} {g : B} {t : ℕ} (l : GiantSignedBirthLineage d s g t)
    (hd : GiantSignedBirthDistinct d) : M + s.2.2.1 g ≤ (PB g).card := by
  simpa only [GiantSignedStateLiveSlots, GiantSignedLiveSlots, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_coe] using Fintype.card_le_of_injective _ (giantSignedBirthLineage_injective l hd)

end
end ArtinMatthews
