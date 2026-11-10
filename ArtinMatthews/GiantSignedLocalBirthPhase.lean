module

public import ArtinMatthews.GiantSignedLocalBirthFrame
public import ArtinMatthews.GiantSignedRawEdgeData
public import ArtinMatthews.GiantSignedUniformBirthRank
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

/-! Local factors read only the births of one actual operation. The same
frame and permutation are used for all pattern choices. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B : Type*} [Fintype B] {PB : B → Finset ℕ} {k ell n H : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}

def giantSignedFrameLocalMultiplier
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) (value : GiantSignedUniformBirthAddress B (k+ell) n H → Option ℕ) : ℂ :=
  ∏ a, if giantSignedUniformBirthOperation (k+ell) n H a = o then
    giantSignedBirthLocalMultiplier σ θ a (value a) else 1

theorem giantSignedFrameLocalMultiplier_norm_le
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) (value : GiantSignedUniformBirthAddress B (k+ell) n H → Option ℕ) :
    ‖giantSignedFrameLocalMultiplier σ θ o value‖ ≤ 1 := by
  rw [giantSignedFrameLocalMultiplier, norm_prod]
  apply Finset.prod_le_one₀
  · intro a _
    exact norm_nonneg _
  · intro a _
    split_ifs
    · exact giantSignedBirthLocalMultiplier_norm_le σ θ a (value a)
    · simp

theorem giantSignedFrameLocalMultiplier_unaffected
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) (value : GiantSignedUniformBirthAddress B (k+ell) n H → Option ℕ)
    (ho : o ∉ σ.support.image (giantSignedUniformBirthOperation (k+ell) n H)) :
    giantSignedFrameLocalMultiplier σ θ o value = 1 := by
  apply Finset.prod_eq_one
  intro a _
  split_ifs with ha
  · have hn : a ∉ σ.support := fun h => ho (Finset.mem_image.mpr ⟨a,h,ha⟩)
    exact ite_eq_right hn
  · rfl

theorem giantSignedFrameLocalMultiplier_eq_uniform
    (d : GiantSignedBirthData PB ell C batch) (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (o : GiantSignedBirthOperation n) (value : GiantSignedUniformBirthAddress B (k+ell) n H → Option ℕ)
    (h : ∀ a, giantSignedUniformBirthOperation (k+ell) n H a = o →
      value a = giantSignedUniformBirthValue d H hH a) :
    giantSignedFrameLocalMultiplier σ θ o value =
      giantSignedUniformBirthOperationMultiplier d hH σ θ o := by
  unfold giantSignedFrameLocalMultiplier giantSignedUniformBirthOperationMultiplier
  apply Finset.prod_congr rfl
  intro a _
  by_cases ha : giantSignedUniformBirthOperation (k+ell) n H a = o
  · simp only [ite_eq_left ha, h a ha]
  · simp only [ite_eq_right ha]

def giantSignedInitialFramePhase
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (a : MarkedPhysicalMarking PB (k+ell)) : ℂ :=
  giantSignedFrameLocalMultiplier σ θ .initial (fun
    | .inl z => some (a z.1 z.2).val
    | .inr _ => none)

def giantSignedEdgeFramePhase {C : B → Finset (Fin k)}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (i : Fin n) (target : MarkedPhysicalMarking PB (k+ell))
    (promoted : (g : B) → Finset (Fin (ell+(C g).card))) : ℂ :=
  giantSignedFrameLocalMultiplier σ θ (.edge i) (fun
    | .inr (.inl z) => giantSignedEdgeFrameValue target promoted z.2.1 z.2.2
    | _ => none)

def giantSignedVisitFramePhase
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (i : Fin (n+1)) (b : B → ℕ) (born : (g : B) → Fin (b g) → PB g) : ℂ :=
  giantSignedFrameLocalMultiplier σ θ (.visit i) (fun
    | .inr (.inr z) => giantSignedVisitFrameValue b born z.2.1 z.2.2
    | _ => none)

theorem giantSignedInitialFramePhase_eq (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ)) :
    giantSignedInitialFramePhase σ θ d.initial = giantSignedUniformBirthOperationMultiplier d hH σ θ .initial := by
  apply giantSignedFrameLocalMultiplier_eq_uniform d hH
  rintro (⟨g,s⟩ | a) ha
  · exact (giantSignedUniformBirthValue_initial d H hH g s).symm
  · rcases a with a | a <;> cases ha

theorem giantSignedEdgeFramePhase_eq (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ)) (i : Fin n) :
    giantSignedEdgeFramePhase σ θ i (d.target i) (d.promoted i) =
      giantSignedUniformBirthOperationMultiplier d hH σ θ (.edge i) := by
  apply giantSignedFrameLocalMultiplier_eq_uniform d hH
  rintro (a | ⟨j,g,s⟩ | a) ha
  · cases ha
  · have hj : j = i := GiantSignedBirthOperation.edge.inj ha
    subst j
    exact (giantSignedUniformBirthValue_edge_frame d hH i g s).symm
  · cases ha

theorem giantSignedVisitFramePhase_eq (d : GiantSignedBirthData PB ell C batch)
    (hH : ∀ i g, batch i g ≤ H)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ)) (i : Fin (n+1)) :
    giantSignedVisitFramePhase (PB := PB) σ θ i (batch i) (d.born i) =
      giantSignedUniformBirthOperationMultiplier d hH σ θ (.visit i) := by
  apply giantSignedFrameLocalMultiplier_eq_uniform d hH
  rintro (a | a | ⟨j,g,s⟩) ha
  · cases ha
  · cases ha
  · have hj : j = i := GiantSignedBirthOperation.visit.inj ha
    subst j
    exact (giantSignedUniformBirthValue_visit_frame d hH i g s).symm

variable {S : Type*} [Fintype S] {PS : S → Finset ℕ}

def giantSignedRawEdgeFramePhase {C : B → Finset (Fin k)}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (i : Fin n) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) : ℂ :=
  giantSignedEdgeFramePhase σ θ i r.bigTarget r.choice.2.1

theorem giantSignedRawEdgeFramePhase_norm_le {C : B → Finset (Fin k)}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (i : Fin n) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) :
    ‖giantSignedRawEdgeFramePhase σ θ i s r‖ ≤ 1 :=
  giantSignedFrameLocalMultiplier_norm_le σ θ (.edge i) _

theorem giantSignedRawEdgeFramePhase_unaffected {C : B → Finset (Fin k)}
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (θ : GiantSignedUniformBirthAddress B (k+ell) n H → AddCircle (1 : ℝ))
    (i : Fin n) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2)
    (hi : .edge i ∉ σ.support.image (giantSignedUniformBirthOperation (k+ell) n H)) :
    giantSignedRawEdgeFramePhase σ θ i s r = 1 :=
  giantSignedFrameLocalMultiplier_unaffected σ θ (.edge i) _ hi

end
end ArtinMatthews
