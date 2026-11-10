module

public import ArtinMatthews.GiantSignedSmallOmissionPermutations
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

/-! The copied small product in the original source-slot average is the
complement of the omitted suffix image. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

section Products
variable {S : Type*} [Fintype S] {P : S → Finset ℕ} {kCopy ell : ℕ}

def giantSignedSmallPermutationCopiedProduct (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) : ℕ :=
  ∏ g, ∏ i : Fin kCopy, (a g (σ g (Fin.castAdd ell i)) : ℕ)

theorem giantSignedSmallPermutationOmittedProduct (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    giantSignedSmallOmittedProduct a (giantSignedSmallPermutationOmission kCopy ell σ) =
      ∏ g, ∏ i : Fin ell, (a g (σ g (Fin.natAdd kCopy i)) : ℕ) := by
  simp only [giantSignedSmallOmittedProduct, giantSignedSmallPermutationOmission,
    giantSignedSmallOmissionSuffix, Finset.prod_map, Function.Embedding.coeFn_mk,
    Equiv.toEmbedding_apply]

theorem giantSignedSmallPermutationCopied_mul_omitted
    (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    giantSignedSmallPermutationCopiedProduct a σ *
      giantSignedSmallOmittedProduct a (giantSignedSmallPermutationOmission kCopy ell σ) =
        markedPhysicalMarkingProduct a := by
  rw [giantSignedSmallPermutationOmittedProduct, giantSignedSmallPermutationCopiedProduct,
    ← Finset.prod_mul_distrib]
  unfold markedPhysicalMarkingProduct
  apply Finset.prod_congr rfl
  intro g _
  rw [← Fin.prod_univ_add (fun i : Fin (kCopy + ell) => (a g (σ g i) : ℕ))]
  exact Equiv.prod_comp (σ g) (fun i => (a g i : ℕ))

theorem giantSignedSmallPermutationCopied_eq (hP : ∀ g q, q ∈ P g → q.Prime)
    (a : MarkedPhysicalMarking P (kCopy + ell))
    (σ : (g : S) → Equiv.Perm (Fin (kCopy + ell))) :
    giantSignedSmallPermutationCopiedProduct a σ =
      giantSignedSmallCopiedProduct a (giantSignedSmallPermutationOmission kCopy ell σ) := by
  apply mul_right_cancel₀
    (giantSignedSmallOmittedProduct_pos hP a (giantSignedSmallPermutationOmission kCopy ell σ)).ne'
  rw [giantSignedSmallPermutationCopied_mul_omitted, giantSignedSmallCopied_mul_omitted]

end Products
end
end ArtinMatthews
