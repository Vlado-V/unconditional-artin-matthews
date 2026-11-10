module

public import ArtinMatthews.GiantSignedMemoryState
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

/-! Old-memory permutations move promotion indices and induce the exact
complement permutation. Store order is preserved. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

section Complement
variable {k a : ℕ}

def giantSignedMovedPromotion (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k) : Fin a ↪ Fin k :=
  e.trans σ.toEmbedding

theorem giantSignedMovedPromotion_mem (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k) (i : Fin k) :
    σ i ∈ Finset.univ.map (giantSignedMovedPromotion σ e) ↔ i ∈ Finset.univ.map e := by
  constructor
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp h
    refine Finset.mem_map.mpr ⟨j, Finset.mem_univ _, ?_⟩
    exact σ.injective hj
  · intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp h
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩

def giantSignedComplementEquiv (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k) :
    ↥((Finset.univ.map e)ᶜ) ≃ ↥((Finset.univ.map (giantSignedMovedPromotion σ e))ᶜ) :=
  σ.subtypeEquiv fun i => by
    simp only [Finset.mem_compl]
    exact (not_congr (giantSignedMovedPromotion_mem σ e i)).symm

def giantSignedComplementOrderEquiv (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k) :
    Fin (Finset.univ.map e)ᶜ.card ≃
      Fin (Finset.univ.map (giantSignedMovedPromotion σ e))ᶜ.card :=
  (((Finset.univ.map e)ᶜ).orderIsoOfFin rfl).toEquiv.trans
    ((giantSignedComplementEquiv σ e).trans
      (((Finset.univ.map (giantSignedMovedPromotion σ e))ᶜ).orderIsoOfFin rfl).toEquiv.symm)

theorem giantSignedComplementOrderEquiv_apply (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k)
    (i : Fin (Finset.univ.map e)ᶜ.card) :
    ((Finset.univ.map (giantSignedMovedPromotion σ e))ᶜ).orderEmbOfFin rfl
        (giantSignedComplementOrderEquiv σ e i) =
      σ (((Finset.univ.map e)ᶜ).orderEmbOfFin rfl i) := by
  let E := (((Finset.univ.map (giantSignedMovedPromotion σ e))ᶜ).orderIsoOfFin rfl).toEquiv
  exact congrArg Subtype.val (E.apply_symm_apply
    (giantSignedComplementEquiv σ e ((((Finset.univ.map e)ᶜ).orderIsoOfFin rfl) i)))

def giantSignedOutputOrderEquiv (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k) (b : ℕ) :
    Fin ((Finset.univ.map e)ᶜ.card + b) ≃
      Fin ((Finset.univ.map (giantSignedMovedPromotion σ e))ᶜ.card + b) :=
  (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (giantSignedComplementOrderEquiv σ e) (Equiv.refl (Fin b)))).trans
    finSumFinEquiv

theorem giantSignedOutputOrderEquiv_left (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k)
    (b : ℕ) (i : Fin (Finset.univ.map e)ᶜ.card) :
    giantSignedOutputOrderEquiv σ e b (Fin.castAdd b i) =
      Fin.castAdd b (giantSignedComplementOrderEquiv σ e i) := by
  simp only [giantSignedOutputOrderEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

theorem giantSignedOutputOrderEquiv_right (σ : Equiv.Perm (Fin k)) (e : Fin a ↪ Fin k)
    (b : ℕ) (i : Fin b) :
    giantSignedOutputOrderEquiv σ e b (Fin.natAdd (Finset.univ.map e)ᶜ.card i) =
      Fin.natAdd (Finset.univ.map (giantSignedMovedPromotion σ e))ᶜ.card i := by
  simp only [giantSignedOutputOrderEquiv, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inr, finSumFinEquiv_apply_right]
end Complement

theorem giantSignedMemorySymmetric_equiv {J : Type*} {P : J → Finset ℕ}
    (f : GiantSignedMemory P → ℂ) (hf : GiantSignedMemorySymmetric f)
    {n k : J → ℕ} (e : (j : J) → Fin (n j) ≃ Fin (k j))
    (u : (j : J) → Fin (k j) → GiantSignedParticle (P j)) :
    f ⟨n, fun j i => u j (e j i)⟩ = f ⟨k, u⟩ := by
  have h : n = k := funext fun j => by
    simpa only [Fintype.card_fin] using Fintype.card_congr (e j)
  subst k
  exact hf ⟨n, u⟩ e

end
end ArtinMatthews
