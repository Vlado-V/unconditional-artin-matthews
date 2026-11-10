module

public import ArtinMatthews.MarkedMemoryActualTableau
public import ArtinMatthews.MarkedMemoryIndependentRelabel
public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction
public import ArtinMatthews.MarkedMemoryBirthAnchor
public import ArtinMatthews.MarkedMemoryFiniteTableauRecovery
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

/-! The birth-position convention removes the unused static-anchor
freedom. Actual extraction with empty initial pending memory obeys this
convention already. It is preserved by relabeling and finite restriction. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A A' : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  [∀ j,Fintype (A' j)] [∀ j,DecidableEq (A' j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

def MarkedMemoryBirthNormalized
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n) : Prop :=
  ∀ j a,d.particle j a=markedRawAnchoredParticle (P j) (d.particle j a).1
    (d.position ((d.lifespan j).first a/2)).1 (hZ _ (d.position ((d.lifespan j).first a/2)).2)

theorem markedMemoryBirthNormalized_relabel
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (hn : MarkedMemoryBirthNormalized hZ d) (e : (j : J) → A j ≃ A' j) :
    MarkedMemoryBirthNormalized hZ (markedMemoryIndependentRelabel hZ e d) := by
  intro j a
  exact hn j ((e j).symm a)

theorem markedMemoryBirthNormalized_relabel_iff
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (e : (j : J) → A j ≃ A' j) :
    MarkedMemoryBirthNormalized hZ (markedMemoryIndependentRelabel hZ e d) ↔
      MarkedMemoryBirthNormalized hZ d := by
  constructor
  · intro hn j a
    simpa only [markedMemoryIndependentRelabel,markedMemoryQueueRelabel,
      Equiv.symm_apply_apply] using hn j (e j a)
  · exact fun hn => markedMemoryBirthNormalized_relabel hZ d hn e

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryBirthNormalized_restore
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (hn : MarkedMemoryBirthNormalized hZ d) :
    MarkedMemoryBirthNormalized hZ
      (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryIndependent_toFinite hZ d)) := by
  intro j a
  have hv : (d.lifespan j).first a/2≤n := by
    have hf := (d.lifespan j).nonempty a
    have hl := (d.lifespan j).bounded a
    omega
  simpa only [markedMemoryFinite_restore_particle,markedMemoryFinite_restore_first,
    markedMemoryFinite_restore_position hZ d _ hv] using hn j a

variable {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryActualTableau_birthNormalized [DecidableEq J]
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) :
    MarkedMemoryBirthNormalized hZ (markedMemoryActualTableau hZ history ha) := by
  intro j a
  exact markedMemoryActualParticle_birthPosition hZ history hempty j a

theorem markedMemoryActualTableau_of_weight_ne_zero_birthNormalized [DecidableEq J]
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (k : ℕ)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k history ≠ 0) :
    MarkedMemoryBirthNormalized hZ
      (markedMemoryActualTableau_of_weight_ne_zero hZ history ν V ψ η d₀ Y Q ρ qStage χ k hw) :=
  markedMemoryActualTableau_birthNormalized hZ history hempty
    (markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ qStage χ n k history hw)

end
end ArtinMatthews
