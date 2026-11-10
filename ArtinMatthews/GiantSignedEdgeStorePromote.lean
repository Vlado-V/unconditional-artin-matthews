module

public import ArtinMatthews.GiantSignedEdgeFixedJoint
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

/-! The literal free-slot row has fresh prime law only on the unpromoted
target slots. Its joint measure has the prime law on every free source and
target slot, with exactly the old-survivor factorial. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

section Basic
variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {t : J → ℕ}

def giantSignedFreePrimeMass (ν : (j : J) → P j → ℂ)
    (c : GiantSignedPrimeTuple P t) : ℂ := ∏ j, ∏ i, ν j (c j i)

def giantSignedFreshPrimeMass (ν : (j : J) → P j → ℂ)
    (T : (j : J) → Finset (Fin (t j))) (c : GiantSignedPrimeTuple P t) : ℂ :=
  ∏ j, ∏ i, ν j ((markedRawSubsetTupleEquiv (T j) (c j)).2 i)

theorem giantSignedSelectedFresh_mass (ν : (j : J) → P j → ℂ)
    (T : (j : J) → Finset (Fin (t j))) (c : GiantSignedPrimeTuple P t) :
    (∏ j, ∏ i, ν j (giantSignedEdgeSelected (T j) (c j) i)) *
      giantSignedFreshPrimeMass ν T c = giantSignedFreePrimeMass ν c := by
  unfold giantSignedFreshPrimeMass giantSignedFreePrimeMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact (markedRawSubsetTupleEquiv_mass (T j) (ν j) (c j)).symm

def giantSignedPromotionCharge (V : J → ℝ) (a : J → ℕ) : ℂ :=
  ∏ j, ((V j : ℂ)⁻¹) ^ a j

def giantSignedPatternFreeTupleEquiv {k ell : ℕ} (C : J → Finset (Fin k)) :
    ((j : J) → GiantTwoSidedPatternFreeSlots (C j) ell → P j) ≃
      GiantSignedPrimeTuple P (fun j => ell + (C j).card) :=
  Equiv.piCongrRight fun j => Equiv.arrowCongr
    (giantSignedPatternFreeSlotEquiv (C j) ell).symm (Equiv.refl _)

theorem giantSignedPatternFreeTupleEquiv_mass {k ell : ℕ}
    (ν : (j : J) → P j → ℂ) (C : J → Finset (Fin k))
    (f : (j : J) → GiantTwoSidedPatternFreeSlots (C j) ell → P j) :
    giantSignedFreePrimeMass ν (giantSignedPatternFreeTupleEquiv C f) =
      ∏ j, ∏ i, ν j (f j i) := by
  unfold giantSignedFreePrimeMass
  apply Finset.prod_congr rfl
  intro j _
  change (∏ i, ν j (f j (giantSignedPatternFreeSlotEquiv (C j) ell i))) = _
  exact Equiv.prod_comp (giantSignedPatternFreeSlotEquiv (C j) ell) (fun i => ν j (f j i))

/-- Free labels are read through the actual original-order free-slot map. -/
def giantSignedPatternFreeLabels {k ell : ℕ} (C : J → Finset (Fin k))
    (source : (j : J) → Fin (k + ell) → P j) :
    GiantSignedPrimeTuple P (fun j => ell + (C j).card) :=
  fun j i => source j (giantTwoSidedPatternFreeSlot (C j) ell
    (giantSignedPatternFreeSlotEquiv (C j) ell i))

end Basic

section PatternSum
variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}

theorem giantSignedPatternFreeTupleEquiv_sum {k ell : ℕ}
    (C : J → Finset (Fin k)) (F : GiantSignedPrimeTuple P (fun j => ell + (C j).card) → ℂ) :
    (∑ f : (j : J) → GiantTwoSidedPatternFreeSlots (C j) ell → P j,
      F (giantSignedPatternFreeTupleEquiv C f)) = ∑ f, F f :=
  Equiv.sum_comp (giantSignedPatternFreeTupleEquiv C) F

end PatternSum

section StorePromote
variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val]
variable {t : J → ℕ}

def giantSignedEdgeJointKernel (ν : (j : J) → P j → ℂ) (ρ : ℝ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ) : ℂ :=
  ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
    giantSignedFreePrimeMass ν source * giantSignedFreePrimeMass ν target *
      ∑ u : GiantSignedParticleTuple P n,
        giantSignedDegreeMass ν u *
          giantSignedEdgeDampedTest ρ (F source target)
            (giantSignedEdgeInput d u (fun j => giantSignedEdgeSelected (T j) (target j)))
            (giantSignedEdgeOutput d u (fun j => giantSignedEdgeSelected (S j) (source j)))

/-- The literal finite choice row at an arbitrary finite memory degree.
The product `D` is fixed before the old-index retrieval is chosen. -/
def giantSignedEdgeApply (ν : (j : J) → P j → ℂ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (D : ℕ) (source : GiantSignedPrimeTuple P t)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P) : ℂ :=
  ∑ S : (j : J) → Finset (Fin (t j)),
    ∑ T : (j : J) → Finset (Fin (t j)),
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

def giantSignedEdgeStorePromotePairing (ν : (j : J) → P j → ℂ) (V : J → ℝ)
    (ρ : ℝ) (d : ℤ) (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ) : ℂ :=
  ∑ source : GiantSignedPrimeTuple P t, ∑ target : GiantSignedPrimeTuple P t,
    giantSignedFreePrimeMass ν source * giantSignedPromotionCharge V (fun j => (T j).card) *
      giantSignedFreshPrimeMass ν T target *
      ∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card),
        giantSignedDegreeMass ν old *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (n j + (T j).card),
            if GiantSignedEdgeHits d ⟨fun j => n j + (T j).card, old⟩ target ⟨S, T, e⟩ then
              giantSignedEdgeDampedTest ρ (F source target)
                ⟨fun j => n j + (T j).card, old⟩
                (giantSignedEdgeTarget d ⟨fun j => n j + (T j).card, old⟩ source ⟨S, T, e⟩)
            else 0

/-- Exact factorial joint of the actual store/promote row, for every finite
survivor degree and every number of unshared source and target slots. -/
theorem giantSignedEdgeStorePromotePairing_eq_joint
    (ν : (j : J) → P j → ℂ) (V : J → ℝ) (ρ : ℝ) (d : ℤ)
    (n : J → ℕ) (S T : (j : J) → Finset (Fin (t j)))
    (F : GiantSignedPrimeTuple P t → GiantSignedPrimeTuple P t →
      GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (hF : ∀ source target out, GiantSignedMemorySymmetric (fun old => F source target old out)) :
    giantSignedEdgeStorePromotePairing ν V ρ d n S T F =
      giantSignedPromotionCharge V (fun j => (T j).card) *
        giantSignedEdgeJointKernel ν ρ d n S T F := by
  classical
  unfold giantSignedEdgeStorePromotePairing giantSignedEdgeJointKernel
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source _
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target _
  have h := giantSignedEdge_fixed_joint (n := n) ν d
    (fun j => giantSignedEdgeSelected (T j) (target j))
    (fun j => giantSignedEdgeSelected (S j) (source j))
    (giantSignedEdgeDampedTest ρ (F source target))
    (giantSignedEdgeDampedTest_symmetric ρ (F source target) (hF source target))
  have he :
      (∑ old : GiantSignedParticleTuple P (fun j => n j + (T j).card),
        giantSignedDegreeMass ν old *
          ∑ e : (j : J) → Fin (T j).card ↪ Fin (n j + (T j).card),
            if GiantSignedEdgeHits d ⟨fun j => n j + (T j).card, old⟩ target ⟨S, T, e⟩ then
              giantSignedEdgeDampedTest ρ (F source target)
                ⟨fun j => n j + (T j).card, old⟩
                (giantSignedEdgeTarget d ⟨fun j => n j + (T j).card, old⟩ source ⟨S, T, e⟩)
            else 0) =
        (∏ j, ∏ i, ν j (giantSignedEdgeSelected (T j) (target j) i)) *
          ∑ u : GiantSignedParticleTuple P n,
            giantSignedDegreeMass ν u * giantSignedEdgeDampedTest ρ (F source target)
              (giantSignedEdgeInput d u (fun j => giantSignedEdgeSelected (T j) (target j)))
              (giantSignedEdgeOutput d u (fun j => giantSignedEdgeSelected (S j) (source j))) := by
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro old _
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    by_cases hh : GiantSignedTupleHits d (fun j => old j ∘ e j)
        (fun j => giantSignedEdgeSelected (T j) (target j))
    · have ha : GiantSignedEdgeHits d ⟨fun j => n j + (T j).card, old⟩ target ⟨S, T, e⟩ := hh
      simp only [hh, ha, ite_true, giantSignedEdgeTarget_eq_output]
    · have ha : ¬ GiantSignedEdgeHits d ⟨fun j => n j + (T j).card, old⟩ target ⟨S, T, e⟩ := hh
      simp only [hh, ha, ite_false]
  rw [he]
  have hm := giantSignedSelectedFresh_mass ν T target
  calc
    _ = giantSignedPromotionCharge V (fun j => (T j).card) *
        (giantSignedFreePrimeMass ν source *
          ((∏ j, ∏ i, ν j (giantSignedEdgeSelected (T j) (target j) i)) *
            giantSignedFreshPrimeMass ν T target)) *
        (∑ u : GiantSignedParticleTuple P n,
          giantSignedDegreeMass ν u * giantSignedEdgeDampedTest ρ (F source target)
            (giantSignedEdgeInput d u (fun j => giantSignedEdgeSelected (T j) (target j)))
            (giantSignedEdgeOutput d u (fun j => giantSignedEdgeSelected (S j) (source j)))) := by ring
    _ = _ := by rw [hm]; ring

end StorePromote
end
end ArtinMatthews
