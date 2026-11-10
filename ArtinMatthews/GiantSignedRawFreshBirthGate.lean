module

public import ArtinMatthews.GiantSignedEdgeFreshMass
public import ArtinMatthews.GiantSignedBirthStageDraws
public import ArtinMatthews.GiantSignedBirthConditionalValues
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

/-! The raw fresh tuple and the chronological birth draw use the same
unpromoted slots in their original order. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] [DecidableEq B] {PB : B → Finset ℕ}
    {k ell n H : ℕ} {t : B → ℕ}

def giantSignedFreshIndexEquiv (T : (g : B) → Finset (Fin (t g))) :
    (Σ g : B, Fin ((T g)ᶜ).card) ≃ (Σ g : B, {j : Fin (t g) // j ∉ T g}) :=
  Equiv.sigmaCongrRight fun g =>
    (((T g)ᶜ).orderIsoOfFin rfl).toEquiv.trans (markedRawFinsetComplEquiv (T g))

def giantSignedRawFreshBirthEmbedding (i : Fin n) (C : B → Finset (Fin k))
    (T : (g : B) → Finset (Fin (ell+(C g).card))) :
    (Σ g : B, Fin ((T g)ᶜ).card) ↪ GiantSignedUniformBirthAddress B (k+ell) n H :=
  (giantSignedFreshIndexEquiv T).toEmbedding.trans (giantSignedEdgeBirthDraw i C T)

def giantSignedRawFreshBirthValues (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (i : Fin n) (C : B → Finset (Fin k)) (T : (g : B) → Finset (Fin (ell+(C g).card)))
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes)
    (fresh : GiantSignedPrimeTuple PB (fun g => ((T g)ᶜ).card)) :
    GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes :=
  giantSignedUniformBirthConditionalValues hPB (giantSignedRawFreshBirthEmbedding i C T)
    old (fun a => fresh a.1 a.2)

def giantSignedRawFreshBirthGate (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H))
    (i : Fin n) (C : B → Finset (Fin k)) (T : (g : B) → Finset (Fin (ell+(C g).card)))
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes)
    (fresh : GiantSignedPrimeTuple PB (fun g => ((T g)ᶜ).card)) : Prop :=
  GiantSignedUniformBirthConditionalGate σ (.edge i)
    (giantSignedRawFreshBirthValues hPB i C T old fresh)

theorem giantSignedRawFreshBirthValues_eq_edgeDraw
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    (i : Fin n) (C : B → Finset (Fin k)) (T : (g : B) → Finset (Fin (ell+(C g).card)))
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes)
    (target : GiantSignedPrimeTuple PB (fun g => ell+(C g).card)) :
    giantSignedRawFreshBirthValues hPB i C T old ((giantSignedEdgeTargetLabelEquiv T) target).2 =
      giantSignedUniformBirthConditionalValues hPB (giantSignedEdgeBirthDraw i C T) old
        (fun a => target a.1 a.2.val) := by
  let A := GiantSignedUniformBirthAddress B (k+ell) n H
  let E := giantSignedFreshIndexEquiv T
  let e : (Σ g : B, Fin ((T g)ᶜ).card) ↪ A := giantSignedRawFreshBirthEmbedding i C T
  let e' : (Σ g : B, {j : Fin (ell+(C g).card) // j ∉ T g}) ↪ A :=
    giantSignedEdgeBirthDraw i C T
  let x (a : Σ g : B, Fin ((T g)ᶜ).card) : PB (giantSignedUniformBirthGroup (e a)) :=
    ((giantSignedEdgeTargetLabelEquiv T) target).2 a.1 a.2
  let y (a : Σ g : B, {j : Fin (ell+(C g).card) // j ∉ T g}) :
      PB (giantSignedUniformBirthGroup (e' a)) := target a.1 a.2.val
  funext a
  change giantSignedUniformBirthConditionalValues hPB e old x a =
    giantSignedUniformBirthConditionalValues hPB e' old y a
  by_cases ha : a ∈ Set.range e
  · obtain ⟨j,rfl⟩ := ha
    have hx := giantSignedUniformBirthConditionalValues_draw hPB e old x j
    have hy : giantSignedUniformBirthConditionalValues hPB e' old y (e j) =
        some (⟨(y (E j)).val,hPB _ _ (y (E j)).property⟩ : Nat.Primes) :=
      giantSignedUniformBirthConditionalValues_draw hPB e' old y (E j)
    have he :
        some (⟨(x j).val,hPB _ _ (x j).property⟩ : Nat.Primes) =
        some (⟨(y (E j)).val,hPB _ _ (y (E j)).property⟩ : Nat.Primes) := by
      rcases j with ⟨g,j⟩
      rfl
    exact hx.trans (he.trans hy.symm)
  · have ha' : a ∉ Set.range e' := by
      rintro ⟨j,hj⟩
      apply ha
      refine ⟨E.symm j,?_⟩
      change e' (E (E.symm j)) = a
      rwa [Equiv.apply_symm_apply]
    rw [giantSignedUniformBirthConditionalValues_outside hPB e old x a ha,
      giantSignedUniformBirthConditionalValues_outside hPB e' old y a ha']

theorem giantSignedRawFreshBirthValues_eq_stageTuple
    (hPB : ∀ g p, p ∈ PB g → p.Prime)
    {C : Fin n → B → Finset (Fin k)} {b : Fin (n+1) → B → ℕ}
    (d : GiantSignedBirthData PB ell C b) (hH : ∀ i g, b i g ≤ H) (i : Fin n)
    (old : GiantSignedUniformBirthAddress B (k+ell) n H → Option Nat.Primes) :
    giantSignedRawFreshBirthValues hPB i (C i) (d.promoted i) old
      ((giantSignedEdgeTargetLabelEquiv (d.promoted i)) (giantSignedPatternFreeLabels (C i) (d.target i))).2 =
      giantSignedUniformBirthConditionalValues hPB (giantSignedBirthStageEmbedding d hH (.edge i))
        old (giantSignedBirthStageTuple d hH (.edge i)) :=
  giantSignedRawFreshBirthValues_eq_edgeDraw hPB i (C i) (d.promoted i) old
    (giantSignedPatternFreeLabels (C i) (d.target i))

end
end ArtinMatthews
