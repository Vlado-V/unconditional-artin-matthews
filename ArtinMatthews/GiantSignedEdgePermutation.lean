module

public import ArtinMatthews.MarkedMinorArcRawMemoryGroupedSubset
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

/-! Ordered retrievals act on the final block of the canonical old tuple. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedAppendPermutation (n a : ℕ) (σ : Equiv.Perm (Fin a)) :
    Equiv.Perm (Fin (n + a)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin n)) σ)).trans finSumFinEquiv

theorem giantSignedAppendPermutation_left {n a : ℕ} (σ : Equiv.Perm (Fin a)) (i : Fin n) :
    giantSignedAppendPermutation n a σ (Fin.castAdd a i) = Fin.castAdd a i := by
  simp only [giantSignedAppendPermutation, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem giantSignedAppendPermutation_right {n a : ℕ} (σ : Equiv.Perm (Fin a)) (i : Fin a) :
    giantSignedAppendPermutation n a σ (Fin.natAdd n i) = Fin.natAdd n (σ i) := by
  simp only [giantSignedAppendPermutation, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

theorem giantSignedAppend_comp_permutation {X : Type*} {n a : ℕ}
    (u : Fin n → X) (p : Fin a → X) (σ : Equiv.Perm (Fin a)) :
    Fin.append u (p ∘ σ) = (Fin.append u p) ∘ giantSignedAppendPermutation n a σ := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Fin.append_left, Function.comp_apply, giantSignedAppendPermutation_left]
  · intro j
    simp only [Fin.append_right, Function.comp_apply, giantSignedAppendPermutation_right]

def giantSignedGroupedTuplePermutation {J : Type*} {X : J → Type*} {a : J → ℕ}
    (σ : (j : J) → Equiv.Perm (Fin (a j))) :
    ((j : J) → Fin (a j) → X j) ≃ ((j : J) → Fin (a j) → X j) where
  toFun p j i := p j (σ j i)
  invFun p j i := p j ((σ j).symm i)
  left_inv p := by funext j i; simp
  right_inv p := by funext j i; simp

theorem giantSignedGroupedTuplePermutation_mass {J : Type*} [Fintype J]
    {X : J → Type*} {a : J → ℕ} (μ : (j : J) → X j → ℂ)
    (σ : (j : J) → Equiv.Perm (Fin (a j))) (p : (j : J) → Fin (a j) → X j) :
    (∏ j, ∏ i, μ j (giantSignedGroupedTuplePermutation σ p j i)) = ∏ j, ∏ i, μ j (p j i) := by
  classical
  apply Finset.prod_congr rfl
  intro j _
  exact Equiv.prod_comp (σ j) (fun i => μ j (p j i))

theorem giantSignedGroupedTupleSymmetric_append_right {J : Type*} {X : J → Type*}
    {n a : J → ℕ} (G : ((j : J) → Fin (n j + a j) → X j) → ℂ)
    (hG : MarkedRawGroupedTupleSymmetric (fun j => n j + a j) G)
    (u : (j : J) → Fin (n j) → X j) (p : (j : J) → Fin (a j) → X j)
    (σ : (j : J) → Equiv.Perm (Fin (a j))) :
    G (fun j => Fin.append (u j) (p j ∘ σ j)) = G (fun j => Fin.append (u j) (p j)) := by
  have he : (fun j => Fin.append (u j) (p j ∘ σ j)) =
      fun j => (Fin.append (u j) (p j)) ∘ giantSignedAppendPermutation (n j) (a j) (σ j) := by
    funext j
    exact giantSignedAppend_comp_permutation (u j) (p j) (σ j)
  rw [he]
  exact hG _ _

end
end ArtinMatthews
