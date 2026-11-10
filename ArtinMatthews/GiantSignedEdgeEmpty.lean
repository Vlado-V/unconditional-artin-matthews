module

public import ArtinMatthews.GiantSignedEdgeStorePromote
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

/-! The actual zero-store, zero-promotion summand translates every old
particle and draws all free target labels from the original fresh law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem giantSignedRetrievalSurvivors_empty {X : Type*} {n : ℕ}
    (e : Fin 0 ↪ Fin n) (old : Fin n → X) :
    giantSignedRetrievalSurvivors e old = old := by
  classical
  have hR : Finset.univ.map e = (∅ : Finset (Fin n)) := by simp
  unfold giantSignedRetrievalSurvivors markedRawSurvivorTupleCast
  funext i
  rw [markedRawSubsetTupleEquiv_survivor]
  apply congrArg old
  have hc : ((∅ : Finset (Fin n))ᶜ).card = n := by simp
  have hi : (fun j : Fin n => j) = ((∅ : Finset (Fin n))ᶜ).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc (fun _ => by simp) strictMono_id
  calc
    _ = ((∅ : Finset (Fin n))ᶜ).orderEmbOfFin hc i := by
      simp only [hR]
      exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
    _ = i := (congrFun hi i).symm

theorem giantSignedEdgeTarget_empty {J : Type*} {P : J → Finset ℕ} {t : J → ℕ}
    (d : ℤ) (m : GiantSignedMemory P) (source : GiantSignedPrimeTuple P t)
    (e : (j : J) → Fin 0 ↪ Fin (m.1 j)) :
    giantSignedEdgeTarget d m source ⟨fun _ => ∅, fun _ => ∅, e⟩ =
      giantSignedMemoryTranslate d m := by
  classical
  rcases m with ⟨n, old⟩
  erw [giantSignedEdgeTarget_eq_output (n := n)]
  have he : (fun j => giantSignedRetrievalSurvivors (e j) (old j)) = old :=
    funext (fun j => giantSignedRetrievalSurvivors_empty (e j) (old j))
  erw [he]
  apply congrArg (fun u : (j : J) → Fin (n j) → GiantSignedParticle (P j) =>
    (⟨n, u⟩ : GiantSignedMemory P))
  funext j i
  exact Fin.append_left _ _ i

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

def giantSignedEdgeFixedApply (ν : (j : J) → P j → ℂ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P) (S T : (j : J) → Finset (Fin (t j))) : ℂ :=
  ∑ target : GiantSignedPrimeTuple P t,
    giantSignedPromotionCharge V (fun j => (T j).card) *
      giantSignedFreshPrimeMass ν T target *
      ∑ e : (j : J) → Fin (T j).card ↪ Fin (m.1 j),
        if GiantSignedEdgeHits d m target ⟨S, T, e⟩ ∧
            GiantSignedEdgePromotionBan D T target then
          (giantSignedPendingDamping ρ m : ℂ) *
            (giantSignedPendingDamping ρ (giantSignedEdgeTarget d m source ⟨S, T, e⟩) : ℂ) *
            f target (giantSignedEdgeTarget d m source ⟨S, T, e⟩)
        else 0

theorem giantSignedEdgeApply_eq_sum_fixed (ν : (j : J) → P j → ℂ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P) :
    giantSignedEdgeApply ν V ρ d D source f m =
      ∑ S, ∑ T, giantSignedEdgeFixedApply ν V ρ d D source f m S T := rfl

theorem giantSignedEdgeFixedApply_empty (ν : (j : J) → P j → ℂ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P) :
    giantSignedEdgeFixedApply ν V ρ d D source f m (fun _ => ∅) (fun _ => ∅) =
      (giantSignedPendingDamping ρ m : ℂ) *
        (giantSignedPendingDamping ρ (giantSignedMemoryTranslate d m) : ℂ) *
        ∑ target : GiantSignedPrimeTuple P t,
          giantSignedFreePrimeMass ν target * f target (giantSignedMemoryTranslate d m) := by
  classical
  let empty : (j : J) → Fin 0 ↪ Fin (m.1 j) :=
    fun _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have he (e : (j : J) → Fin 0 ↪ Fin (m.1 j)) : e = empty := by
    funext j
    apply Function.Embedding.ext
    intro i
    exact Fin.elim0 i
  have hh (target : GiantSignedPrimeTuple P t) :
      GiantSignedEdgeHits d m target ⟨fun _ => ∅, fun _ => ∅, empty⟩ ∧
        GiantSignedEdgePromotionBan D (fun _ => ∅) target := by
    constructor <;> intro j i <;> exact Fin.elim0 i
  have hm (target : GiantSignedPrimeTuple P t) :
      giantSignedFreshPrimeMass ν (fun _ => ∅) target = giantSignedFreePrimeMass ν target := by
    have hp : (∏ j, ∏ i, ν j (giantSignedEdgeSelected (∅ : Finset (Fin (t j)))
        (target j) i)) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      apply Finset.prod_eq_one
      intro i _
      exact (Nat.not_lt_zero _ (by simpa only [Finset.card_empty] using i.isLt)).elim
    have hm := giantSignedSelectedFresh_mass ν (fun _ => ∅) target
    rwa [hp, one_mul] at hm
  unfold giantSignedEdgeFixedApply
  simp only [Finset.card_empty, giantSignedPromotionCharge, pow_zero, Finset.prod_const_one,
    one_mul, hm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  rw [Finset.sum_eq_single empty]
  · rw [ite_eq_left (hh target), giantSignedEdgeTarget_empty]
    ring
  · intro e _ hne
    exact False.elim (hne (he e))
  · intro h
    exact (h (Finset.mem_univ _)).elim

end
end ArtinMatthews
