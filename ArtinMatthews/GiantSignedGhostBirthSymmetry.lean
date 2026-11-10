module

public import ArtinMatthews.GiantSignedGhostBirthApply
public import ArtinMatthews.GiantSignedEdgeEquivariance
public import ArtinMatthews.GiantSignedGhostSymmetry
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

/-! Permuting old particles relabels their deletion indices and survivor
order. The actual fresh birth array stays fixed, so its multiplier is exact. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {B : Type u} {PB : B → Finset ℕ}

def giantSignedGhostBirthOldEquiv (m : GiantSignedMemory PB)
    (σ : (g : B) → Equiv.Perm (Fin (m.1 g))) :
    GiantSignedGhostMemoryMoves (giantSignedMemoryPermute m σ) ≃ GiantSignedGhostMemoryMoves m :=
  Equiv.piCongrRight (fun g => Equiv.sigmaCongr (Equiv.finsetCongr (σ g)) (fun _ => Equiv.refl _))

theorem giantSignedGhostBirthOldEquiv_apply (m : GiantSignedMemory PB)
    (σ : (g : B) → Equiv.Perm (Fin (m.1 g)))
    (r : GiantSignedGhostMemoryMoves (giantSignedMemoryPermute m σ)) (g : B) :
    giantSignedGhostBirthOldEquiv m σ r g = ⟨(r g).1.map (σ g).toEmbedding, (r g).2⟩ := rfl

theorem giantSignedGhostBirthOldEquiv_coefficient [Fintype B]
    (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (m : GiantSignedMemory PB) (σ : (g : B) → Equiv.Perm (Fin (m.1 g)))
    (r : GiantSignedGhostMemoryMoves (giantSignedMemoryPermute m σ)) :
    giantSignedGhostMemoryMoveCoefficient ν A C D (giantSignedMemoryPermute m σ) r =
      giantSignedGhostMemoryMoveCoefficient ν A C D m (giantSignedGhostBirthOldEquiv m σ r) := by
  classical
  simp only [giantSignedGhostMemoryMoveCoefficient, giantSignedGhostProductMoveCoefficient]
  apply Finset.prod_congr rfl
  intro g _
  let x : GiantSignedGroupMemory (PB g) := ⟨m.1 g, m.2 g⟩
  let y : GiantSignedGroupMemory (PB g) := ⟨m.1 g, m.2 g ∘ σ g⟩
  let R : Finset (Fin (m.1 g)) := (r g).1
  have hz : (giantSignedGhostZeroIndices y).map (σ g).toEmbedding = giantSignedGhostZeroIndices x :=
    giantSignedGhostZeroIndices_map (m.2 g) (σ g)
  have hc : (giantSignedGhostZeroIndices y).card = (giantSignedGhostZeroIndices x).card := by
    rw [← hz, Finset.card_map]
  have hsub : R ⊆ giantSignedGhostZeroIndices y ↔
      R.map (σ g).toEmbedding ⊆ giantSignedGhostZeroIndices x := by
    rw [← hz]
    exact Finset.map_subset_map.symm
  change giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) y (r g) =
    giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) x ⟨R.map (σ g).toEmbedding, (r g).2⟩
  unfold giantSignedGhostMoveCoefficient
  change (if R ⊆ giantSignedGhostZeroIndices y then _ else 0) =
    if R.map (σ g).toEmbedding ⊆ giantSignedGhostZeroIndices x then _ else 0
  by_cases h : R.map (σ g).toEmbedding ⊆ giantSignedGhostZeroIndices x
  · rw [ite_eq_left (hsub.mpr h), ite_eq_left h, hc, Finset.card_map]
  · rw [ite_eq_right (fun hn => h (hsub.mp hn)), ite_eq_right h]

theorem giantSignedGhostBirthOldEquiv_target_test
    (f : GiantSignedMemory PB → ℂ) (hf : GiantSignedMemorySymmetric f)
    (m : GiantSignedMemory PB) (σ : (g : B) → Equiv.Perm (Fin (m.1 g)))
    (r : GiantSignedGhostMemoryMoves (giantSignedMemoryPermute m σ)) :
    f (giantSignedGhostMemoryMoveTarget (giantSignedMemoryPermute m σ) r) =
      f (giantSignedGhostMemoryMoveTarget m (giantSignedGhostBirthOldEquiv m σ r)) := by
  let t := giantSignedGhostMemoryMoveTarget (giantSignedMemoryPermute m σ) r
  let u := giantSignedGhostMemoryMoveTarget m (giantSignedGhostBirthOldEquiv m σ r)
  let e (g : B) : Fin (t.1 g) ≃ Fin (u.1 g) :=
    giantSignedGhostAppendEquiv (giantSignedGhostSurvivorIndexEquiv (σ g) (r g).1) (r g).2.1
  have he (g : B) (i : Fin (t.1 g)) : t.2 g i = u.2 g (e g i) := by
    let a : GiantSignedGroupMemory (PB g) := ⟨m.1 g, m.2 g⟩
    let a' : GiantSignedGroupMemory (PB g) := ⟨m.1 g, m.2 g ∘ σ g⟩
    let b := (r g).2.2
    let R : Finset (Fin (m.1 g)) := (r g).1
    let R' := R.map (σ g).toEmbedding
    change Fin ((Rᶜ).card+(r g).2.1) at i
    change (giantSignedGhostTarget a' R b).2 i =
      (giantSignedGhostTarget a R' b).2
        (giantSignedGhostAppendEquiv (giantSignedGhostSurvivorIndexEquiv (σ g) R) (r g).2.1 i)
    refine Fin.addCases ?_ ?_ i
    · intro j
      let j' := giantSignedGhostSurvivorIndexEquiv (σ g) R j
      have hp : a'.2 ((Rᶜ).orderEmbOfFin rfl j) = a.2 ((R'ᶜ).orderEmbOfFin rfl j') :=
        (congrArg (m.2 g) (giantSignedGhostSurvivorIndexEquiv_spec (σ g) R j)).symm
      have hj := giantSignedGhostAppendEquiv_left (giantSignedGhostSurvivorIndexEquiv (σ g) R) (r g).2.1 j
      exact (giantSignedGhostTarget_survivor a' R b j).trans
        (hp.trans ((giantSignedGhostTarget_survivor a R' b j').symm.trans
          (congrArg (giantSignedGhostTarget a R' b).2 hj).symm))
    · intro j
      have hj := giantSignedGhostAppendEquiv_right (giantSignedGhostSurvivorIndexEquiv (σ g) R) (r g).2.1 j
      exact (giantSignedGhostTarget_born a' R b j).trans
        ((giantSignedGhostTarget_born a R' b j).symm.trans
          (congrArg (giantSignedGhostTarget a R' b).2 hj).symm)
  have hT : t = ⟨t.1, fun g i => u.2 g (e g i)⟩ :=
    (Sigma.eta t).symm.trans (congrArg (Sigma.mk t.1) (funext fun g => funext (he g)))
  exact (congrArg f hT).trans
    ((giantSignedMemorySymmetric_equiv f hf e u.2).trans (congrArg f (Sigma.eta u)))

variable {S : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {M : ℕ}

theorem giantSignedStateGhostBirthApply_memorySymmetric
    (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ) (φ : GiantSignedGhostBirthMultiplier PB)
    (f : GiantSignedState PS PB M → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedStateGhostBirthApply PS ν A C D φ f (s,a,m)) := by
  intro s a m σ
  let e := giantSignedGhostBirthOldEquiv m σ
  let w (r : GiantSignedGhostMemoryMoves m) :=
    giantSignedGhostMemoryMoveCoefficient ν A C D m r *
      φ (fun g => (r g).2.1) (fun g => (r g).2.2) *
      f (s,a,giantSignedGhostMemoryMoveTarget m r)
  change _ = ∑' r, w r
  rw [← e.tsum_eq w]
  apply tsum_congr
  intro r
  have hc := giantSignedGhostBirthOldEquiv_coefficient ν A C D m σ r
  have ht := giantSignedGhostBirthOldEquiv_target_test (fun m => f (s,a,m)) (hf s a) m σ r
  have hphi : φ (fun g => (r g).2.1) (fun g => (r g).2.2) =
      φ (fun g => (e r g).2.1) (fun g => (e r g).2.2) := rfl
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hc hphi) ht

theorem giantSignedProjectedBirthVisit_memorySymmetric (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (qi ρ : ℝ) (φ : GiantSignedGhostBirthMultiplier PB)
    (f : GiantSignedState PS PB M → ℂ)
    (hf : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric
      (fun m => giantSignedProjectedBirthVisit H ν V qi ρ φ f (s,a,m)) := by
  apply giantSignedStateMemoryCutoff_memory_symmetric
  exact giantSignedStateGhostBirthApply_memorySymmetric ν _ _ _ φ _
    (giantSignedStateMemoryCutoff_memory_symmetric H f hf)

end
end ArtinMatthews
