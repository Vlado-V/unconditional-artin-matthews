module

public import ArtinMatthews.GiantSignedUniformBirthFrame
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

/-! The full canonical marking splits into copied slots and the actual
free-slot carrier of the edge row. Both injections are the source slot maps. -/
namespace ArtinMatthews
noncomputable section

def giantSignedCanonicalSlotEquiv {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    Fin (k+ell) ≃ {i : Fin k // i ∉ C} ⊕ Fin (ell+C.card) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr
      ((Equiv.sumCompl (fun i : Fin k => i ∈ C)).symm.trans (Equiv.sumComm _ _))
      (Equiv.refl (Fin ell))).trans
      ((Equiv.sumAssoc _ _ _).trans
        (Equiv.sumCongr (Equiv.refl _) (giantSignedPatternFreeSlotEquiv C ell).symm)))

theorem giantSignedCanonicalSlotEquiv_symm_copied {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : {i : Fin k // i ∉ C}) :
    (giantSignedCanonicalSlotEquiv C ell).symm (.inl i) = Fin.castAdd ell i.val := rfl

theorem giantSignedCanonicalSlotEquiv_symm_free {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : Fin (ell+C.card)) :
    (giantSignedCanonicalSlotEquiv C ell).symm (.inr i) = giantSignedFreeSlotEmbedding C ell i := by
  change _ = giantTwoSidedPatternFreeSlot C ell (giantSignedPatternFreeSlotEquiv C ell i)
  unfold giantSignedCanonicalSlotEquiv
  simp only [Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.symm_symm,
    Equiv.sumCongr_apply, Sum.map_inr]
  generalize giantSignedPatternFreeSlotEquiv C ell i = s
  cases s <;> rfl

theorem giantSignedCanonicalSlotEquiv_copied {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : {i : Fin k // i ∉ C}) :
    giantSignedCanonicalSlotEquiv C ell (Fin.castAdd ell i.val) = .inl i := by
  rw [← giantSignedCanonicalSlotEquiv_symm_copied C ell i, Equiv.apply_symm_apply]

theorem giantSignedCanonicalSlotEquiv_free {k : ℕ} (C : Finset (Fin k)) (ell : ℕ)
    (i : Fin (ell+C.card)) :
    giantSignedCanonicalSlotEquiv C ell (giantSignedFreeSlotEmbedding C ell i) = .inr i := by
  rw [← giantSignedCanonicalSlotEquiv_symm_free C ell i, Equiv.apply_symm_apply]

end
end ArtinMatthews
