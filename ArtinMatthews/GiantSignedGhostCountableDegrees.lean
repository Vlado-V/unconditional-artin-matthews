module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkFactorial
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! All ghost degrees are reindexed by the actual surviving, deleted
and born counts, with the original deletion subset retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

@[ext] structure GiantSignedGhostDegrees where
  survivors : ℕ
  deleted : ℕ
  born : ℕ

abbrev GiantSignedGhostRawShape := Σ k : ℕ, Finset (Fin k) × ℕ

abbrev GiantSignedGhostDegreeShape :=
  Σ d : GiantSignedGhostDegrees, MarkedRawDeletionBatch (d.survivors + d.deleted) d.deleted

def giantSignedGhostDegreeToRaw (a : GiantSignedGhostDegreeShape) : GiantSignedGhostRawShape :=
  ⟨a.1.survivors + a.1.deleted, a.2.val, a.1.born⟩

theorem giantSignedGhostDegreeToRaw_injective : Function.Injective giantSignedGhostDegreeToRaw := by
  intro a b hab
  have hd : a.1.deleted = b.1.deleted := by
    have h := congrArg (fun s : GiantSignedGhostRawShape => s.2.1.card) hab
    exact (markedRawDeletionBatch_deleted_card a.2).symm.trans
      (h.trans (markedRawDeletionBatch_deleted_card b.2))
  have hn : a.1.survivors = b.1.survivors := by
    have h := congrArg (fun s : GiantSignedGhostRawShape => s.2.1ᶜ.card) hab
    exact (markedRawDeletionBatch_survivor_card rfl a.2).symm.trans
      (h.trans (markedRawDeletionBatch_survivor_card rfl b.2))
  have hb : a.1.born = b.1.born := congrArg (fun s : GiantSignedGhostRawShape => s.2.2) hab
  have he : a.1 = b.1 := GiantSignedGhostDegrees.ext hn hd hb
  rcases a with ⟨a, A⟩
  rcases b with ⟨b, B⟩
  dsimp only at he
  cases he
  have htail := eq_of_heq (Sigma.mk.inj_iff.mp hab).2
  have hAB : A = B := Subtype.ext (congrArg Prod.fst htail)
  cases hAB
  rfl

theorem giantSignedGhostDegreeToRaw_surjective : Function.Surjective giantSignedGhostDegreeToRaw := by
  classical
  rintro ⟨k, S, b⟩
  let d : GiantSignedGhostDegrees := ⟨Sᶜ.card, S.card, b⟩
  have hn : Sᶜ.card = d.survivors := rfl
  have hd : S.card = d.deleted := rfl
  have hb : b = d.born := rfl
  have hk : d.survivors + d.deleted = k := by
    rw [← hn, ← hd, Finset.card_compl, Fintype.card_fin]
    have hs : S.card ≤ k := by simpa using Finset.card_le_card (Finset.subset_univ S)
    omega
  clear_value d
  cases hk
  let A : MarkedRawDeletionBatch (d.survivors + d.deleted) d.deleted :=
    ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hd⟩⟩
  refine ⟨⟨d, A⟩, ?_⟩
  dsimp only [giantSignedGhostDegreeToRaw, A]
  rw [← hb]

def giantSignedGhostDegreeEquiv : GiantSignedGhostDegreeShape ≃ GiantSignedGhostRawShape :=
  Equiv.ofBijective giantSignedGhostDegreeToRaw
    ⟨giantSignedGhostDegreeToRaw_injective, giantSignedGhostDegreeToRaw_surjective⟩

theorem giantSignedGhostDegree_tsum (f : GiantSignedGhostRawShape → ℂ) :
    (∑' d : GiantSignedGhostDegreeShape, f (giantSignedGhostDegreeToRaw d)) = ∑' r, f r :=
  giantSignedGhostDegreeEquiv.tsum_eq f

end
end ArtinMatthews
