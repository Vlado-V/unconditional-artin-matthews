module

public import ArtinMatthews.GiantSignedMemoryState
public import ArtinMatthews.MarkedMinorArcRawMemoryBulkIndices
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual old-index promotions and source-slot stores for all finite
memory degrees. Every survivor is translated before the stores are appended. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedEdgeChoice {J : Type*} (t d : J → ℕ) :=
  Σ _ : (j : J) → Finset (Fin (t j)),
    Σ T : (j : J) → Finset (Fin (t j)),
      (j : J) → Fin ((T j).card) ↪ Fin (d j)

def giantSignedEdgeSelected {P : Finset ℕ} {t : ℕ}
    (S : Finset (Fin t)) (a : Fin t → P) : Fin S.card → P :=
  fun i => a (S.orderEmbOfFin rfl i)

def giantSignedParticleAt {P : Finset ℕ} (r : ℤ) (p : P) : GiantSignedParticle P :=
  ⟨p, (r : ZMod p.val)⟩

theorem giantSignedParticleTranslate_at {P : Finset ℕ} (d r : ℤ) (p : P) :
    giantSignedParticleTranslate d (giantSignedParticleAt r p) =
      giantSignedParticleAt (r + d) p := by
  simp only [giantSignedParticleTranslate, giantSignedParticleAt, Equiv.coe_fn_mk, Int.cast_add]

theorem giantSignedParticleTranslate_neg {P : Finset ℕ} (d : ℤ)
    (p : GiantSignedParticle P) :
    giantSignedParticleTranslate (-d) (giantSignedParticleTranslate d p) = p := by
  rcases p with ⟨p, r⟩
  simp [giantSignedParticleTranslate]

theorem giantSignedParticleTranslate_zero_iff {P : Finset ℕ} (d : ℤ)
    (p : GiantSignedParticle P) (q : P) :
    giantSignedParticleTranslate d p = giantSignedParticleAt 0 q ↔
      p = giantSignedParticleAt (-d) q := by
  constructor
  · intro h
    have e := congrArg (giantSignedParticleTranslate (-d)) h
    simpa only [giantSignedParticleTranslate_neg, giantSignedParticleTranslate_at,
      zero_add] using e
  · rintro rfl
    rw [giantSignedParticleTranslate_at, neg_add_cancel]

def giantSignedEdgeRetrievedIndices {J : Type*} {t d : J → ℕ}
    (c : GiantSignedEdgeChoice t d) (j : J) : Finset (Fin (d j)) :=
  Finset.univ.map (c.2.2 j)

def giantSignedEdgeTarget {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (source : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) : GiantSignedMemory P :=
  ⟨fun j => ((giantSignedEdgeRetrievedIndices c j)ᶜ).card + (c.1 j).card,
    fun j => Fin.append
      (fun i => giantSignedParticleTranslate d
        ((markedRawSubsetTupleEquiv (giantSignedEdgeRetrievedIndices c j) (m.2 j)).2 i))
      (fun i => giantSignedParticleAt d (giantSignedEdgeSelected (c.1 j) (source j) i))⟩

theorem giantSignedEdgeTarget_degree {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (source : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) (j : J) :
    (giantSignedEdgeTarget d m source c).1 j = m.1 j - (c.2.1 j).card + (c.1 j).card := by
  classical
  simp only [giantSignedEdgeTarget, giantSignedEdgeRetrievedIndices, Finset.card_compl,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem giantSignedEdgeTarget_survivor {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (source : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) (j : J)
    (i : Fin ((giantSignedEdgeRetrievedIndices c j)ᶜ).card) :
    (giantSignedEdgeTarget d m source c).2 j (Fin.castAdd (c.1 j).card i) =
      giantSignedParticleTranslate d (m.2 j ((giantSignedEdgeRetrievedIndices c j)ᶜ.orderEmbOfFin rfl i)) := by
  simp only [giantSignedEdgeTarget, Fin.append_left, markedRawSubsetTupleEquiv_survivor]

theorem giantSignedEdgeTarget_store {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (source : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) (j : J) (i : Fin (c.1 j).card) :
    (giantSignedEdgeTarget d m source c).2 j
        (Fin.natAdd ((giantSignedEdgeRetrievedIndices c j)ᶜ).card i) =
      giantSignedParticleAt d (source j ((c.1 j).orderEmbOfFin rfl i)) := by
  simp only [giantSignedEdgeTarget, Fin.append_right, giantSignedEdgeSelected]

def GiantSignedEdgeHits {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (target : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) : Prop :=
  ∀ j i, giantSignedParticleTranslate d (m.2 j (c.2.2 j i)) =
    giantSignedParticleAt 0 (giantSignedEdgeSelected (c.2.1 j) (target j) i)

theorem giantSignedEdgeHits_iff {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (target : (j : J) → Fin (t j) → P j)
    (c : GiantSignedEdgeChoice t m.1) :
    GiantSignedEdgeHits d m target c ↔
      ∀ j i, m.2 j (c.2.2 j i) =
        giantSignedParticleAt (-d) (giantSignedEdgeSelected (c.2.1 j) (target j) i) := by
  simp only [GiantSignedEdgeHits, giantSignedParticleTranslate_zero_iff]

def GiantSignedEdgePromotionBan {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (D : ℕ) (T : (j : J) → Finset (Fin (t j)))
    (target : (j : J) → Fin (t j) → P j) : Prop :=
  ∀ j i, ¬ (giantSignedEdgeSelected (T j) (target j) i).val ∣ D

end
end ArtinMatthews
