module

public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
public import ArtinMatthews.MarkedMinorArcRawGhostHits
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact rho cancellation in the literal signed ghost choice, using the
actual old, deleted, surviving and newly born indexed hit counts. All
signs and birth factorial measures remain present. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

/-- Each old deletion, surviving hit, and new birth cancels exactly its
adjacent edge damping factors. -/
theorem markedMemory_ghost_rho_group (ρ a q b : ℝ) (hρ : ρ ≠ 0)
    (h d l : ℕ) (hd : d ≤ h) :
    ρ^h*((a/ρ)^d*(q/ρ^2)^(h-d)*(b/ρ)^l)*ρ^(h-d+l) =
      a^d*q^(h-d)*b^l := by
  have hh : ρ^h = ρ^(h-d)*ρ^d := by rw [← pow_add, Nat.sub_add_cancel hd]
  calc
    _ = (ρ*(a/ρ))^d*(ρ*(q/ρ^2)*ρ)^(h-d)*((b/ρ)*ρ)^l := by
      rw [hh]
      simp only [pow_add, mul_pow]
      ring
    _ = _ := by
      have ha : ρ*(a/ρ)=a := by field_simp
      have hq : ρ*(q/ρ^2)*ρ=q := by field_simp
      have hb : (b/ρ)*ρ=b := by field_simp
      rw [ha,hq,hb]

def markedMemoryGhostReducedCoefficient {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) : ℝ :=
  ∏ j, (-(1-qStage))^(del j).card *
    qStage^((markedRawGroupHitIndices m j z hz \ del j).card) *
      (-(1-qStage)*V j)^(l.1 j : ℕ)

/-- Actual aggregate cancellation, with no assumption on signs of q or V. -/
theorem markedMemoryGhost_signed_rho_cancellation {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage ρ : ℝ) (hρ : ρ ≠ 0)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (hdel : MarkedRawGhostDeletionAllowed m z hz del)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    ρ^(markedRawPendingHits m z hz) * markedRawGhostSignedCoefficient V qStage ρ m z hz del l *
      ρ^(markedRawPendingHits (markedRawGhostTargetMemory m z hz del l births) z hz) =
        markedMemoryGhostReducedCoefficient V qStage m z hz del l := by
  rw [markedRawPendingHits_eq_sum_card,markedRawGhostTargetMemory_total_hits m z hz del hdel l births]
  rw [← Finset.prod_pow_eq_pow_sum,← Finset.prod_pow_eq_pow_sum]
  unfold markedRawGhostSignedCoefficient markedMemoryGhostReducedCoefficient
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.card_sdiff_of_subset (hdel j)]
  exact markedMemory_ghost_rho_group ρ (-(1-qStage)) qStage (-(1-qStage)*V j) hρ
    (markedRawGroupHitIndices m j z hz).card (del j).card (l.1 j : ℕ) (Finset.card_le_card (hdel j))

/-- The exact signed choice term keeps its actual ordered birth mass and
all individual factorials after cancellation. -/
theorem markedMemoryGhostChoice_rho_cancellation {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) (hρ : ρ ≠ 0) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) :
    ((ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ) *
        markedMemoryGhostChoiceWeight ν V qStage ρ hZ s choice *
      ((ρ^(markedRawPendingHits (markedMemoryGhostChoiceTarget hZ s choice).2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ) =
    ((markedMemoryGhostReducedCoefficient V qStage s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes *
      markedRawGhostBirthMass ν choice.sizes choice.births : ℝ) : ℂ) := by
  have hc := markedMemoryGhost_signed_rho_cancellation V qStage ρ hρ s.2.2 s.1.1 (hZ _ s.1.2)
    choice.deletion choice.allowed choice.sizes choice.births
  have hr : ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) *
      (markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes *
        markedRawGhostBirthMass ν choice.sizes choice.births) *
      ρ^(markedRawPendingHits (markedMemoryGhostChoiceTarget hZ s choice).2.2 s.1.1 (hZ _ s.1.2)) =
        markedMemoryGhostReducedCoefficient V qStage s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes *
          markedRawGhostBirthMass ν choice.sizes choice.births := by
    calc
      _ = (ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) *
        markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes *
        ρ^(markedRawPendingHits (markedMemoryGhostChoiceTarget hZ s choice).2.2 s.1.1 (hZ _ s.1.2))) *
        markedRawGhostBirthMass ν choice.sizes choice.births := by ring
      _ = _ := congrArg (fun x => x * markedRawGhostBirthMass ν choice.sizes choice.births) hc
  unfold markedMemoryGhostChoiceWeight
  exact_mod_cast hr

/-- Setting rho to one leaves exactly the reduced signed coefficient. -/
theorem markedMemoryGhostReducedCoefficient_eq_one {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) :
    markedMemoryGhostReducedCoefficient V qStage m z hz del l =
      markedRawGhostSignedCoefficient V qStage 1 m z hz del l := by
  simp [markedMemoryGhostReducedCoefficient,markedRawGhostSignedCoefficient]

/-- Exact local identity consumed by whole-history damping telescoping. -/
theorem markedMemoryGhostChoice_rho_eq_one {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) (hρ : ρ ≠ 0) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) :
    ((ρ^(markedRawPendingHits s.2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ) *
        markedMemoryGhostChoiceWeight ν V qStage ρ hZ s choice *
      ((ρ^(markedRawPendingHits (markedMemoryGhostChoiceTarget hZ s choice).2.2 s.1.1 (hZ _ s.1.2)) : ℝ) : ℂ) =
        markedMemoryGhostChoiceWeight ν V qStage 1 hZ s choice := by
  rw [markedMemoryGhostChoice_rho_cancellation ν V qStage ρ hρ hZ s choice,
    markedMemoryGhostReducedCoefficient_eq_one]
  rfl

end
end ArtinMatthews
