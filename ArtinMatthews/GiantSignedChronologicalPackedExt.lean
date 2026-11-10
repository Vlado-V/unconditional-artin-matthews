module

public import ArtinMatthews.GiantSignedChronologicalChoices
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

/-! Equality of chronological data retains every ordered local move,
with heterogeneous equality only for the dependent old-index types. -/

namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch batch' : Fin (n+1) → B → ℕ}

theorem giantSignedChronologicalChoices_heq
    (h : GiantSignedChronologicalChoices PS PB ell C batch)
    (h' : GiantSignedChronologicalChoices PS PB ell C batch')
    (hbatch : batch = batch') (hs : h.state = h'.state)
    (hπS : h.sourceSmallPermutation = h'.sourceSmallPermutation)
    (hτS : h.targetSmallPermutation = h'.targetSmallPermutation)
    (hπB : h.sourceBigPermutation = h'.sourceBigPermutation)
    (hτB : h.targetBigPermutation = h'.targetBigPermutation)
    (haux : h.auxiliary = h'.auxiliary)
    (hghost : ∀ v g, HEq (giantSignedFixedGhostMove (h.state v).2.2 (batch v) (h.deleted v) (h.born v) g)
      (giantSignedFixedGhostMove (h'.state v).2.2 (batch' v) (h'.deleted v) (h'.born v) g))
    (hedge : ∀ i, HEq (h.edge i) (h'.edge i)) : HEq h h' := by
  subst batch'
  rcases h with ⟨state,deleted,born,πS,τS,πB,τB,aux,edge⟩
  rcases h' with ⟨state',deleted',born',πS',τS',πB',τB',aux',edge'⟩
  dsimp only at hs hπS hτS hπB hτB haux hghost hedge
  subst state'
  subst πS'
  subst τS'
  subst πB'
  subst τB'
  subst aux'
  have hd : deleted = deleted' := by
    funext v g
    exact congrArg Sigma.fst (eq_of_heq (hghost v g))
  subst deleted'
  have hb : born = born' := by
    funext v g
    have he := congrArg Sigma.snd (eq_of_heq (hghost v g))
    exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)
  subst born'
  have he : edge = edge' := funext fun i => eq_of_heq (hedge i)
  subst edge'
  rfl

end
end ArtinMatthews
