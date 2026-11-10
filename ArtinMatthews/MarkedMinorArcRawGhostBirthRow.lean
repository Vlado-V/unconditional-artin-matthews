module

public import ArtinMatthews.MarkedMinorArcRawGhostAbsolute
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite ordered-birth integration under the true total-memory
cutoff. The cap is discarded only for a nonnegative absolute row estimate;
the signed ghost action itself keeps every literal cap and coefficient. -/
namespace ArtinMatthews
open scoped BigOperators

noncomputable def markedRawGhostDeletionFactor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (qStage ρ v₀ : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (j : J) : ℝ :=
  ((1-qStage)/(ρ*v₀))^(del j).card*
    (qStage/ρ^2)^((markedRawGroupHitIndices m j z hz \ del j).card)

noncomputable def markedRawGhostBirthFactor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ v₀ : ℝ) (j : J) (l : ℕ) : ℝ :=
  (v₀*(1-qStage)*V j/ρ)^l*(∑ p : P j, ν j p)^l/(Nat.factorial l : ℝ)

theorem markedRawGhostBirthFactor_nonneg {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {qStage ρ v₀ : ℝ}
    (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀) (j : J) (l : ℕ) :
    0 ≤ markedRawGhostBirthFactor ν V qStage ρ v₀ j l := by
  unfold markedRawGhostBirthFactor
  have hc : 0 ≤ v₀*(1-qStage)*V j/ρ :=
    div_nonneg (mul_nonneg (mul_nonneg hv₀.le (sub_nonneg.mpr hq₁)) (hV j)) hρ.le
  exact div_nonneg (mul_nonneg (pow_nonneg hc _)
    (pow_nonneg (Finset.sum_nonneg (fun p _ => hν j p)) _)) (Nat.cast_nonneg _)

/-- Exact literal absolute integration over all actual ordered birth labels
at fixed deletion masks and actual admissible birth sizes. -/
theorem markedRawGhost_absolute_birth_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    {B : ℕ} (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {qStage ρ v₀ : ℝ} (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) :
    (∑ births : MarkedRawGhostBirthLabels l,
      |markedRawGhostSignedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births| *
        (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
          markedRawMemorySchurWeight v₀ m))=
      (∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j)*
        ∏ j, markedRawGhostBirthFactor ν V qStage ρ v₀ j (l.1 j : ℕ) := by
  classical
  simp_rw [markedRawGhost_choice_absolute_weight ν hν V hV hq₀ hq₁ hρ hv₀]
  rw [← Finset.sum_mul,markedRawGhostBirthMass_sum]
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold markedRawGhostAbsoluteFactor markedRawGhostDeletionFactor markedRawGhostBirthFactor
  ring

/-- The true total-cutoff birth-size sum is a sub-sum of the independent
finite group birth-size cube, with the literal same coefficients. -/
theorem markedRawGhost_birth_cap_sum_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) (del : MarkedRawGhostDeletion m)
    (F : (J → Fin (B+1)) → ℝ) (hF : ∀ l, 0 ≤ F l) :
    (∑ l : MarkedRawGhostBirthSizes m del, F l.1) ≤ ∑ l : J → Fin (B+1), F l := by
  classical
  let S := (Finset.univ : Finset (J → Fin (B+1))).filter
    (fun l => ∑ j, ((markedRawGhostSurvivors m del j).card+(l j : ℕ)) ≤ B)
  have hs : (∑ l ∈ S, F l)=(∑ l : MarkedRawGhostBirthSizes m del, F l.1) :=
    Finset.sum_subtype S (by intro x; simp [S]) F
  rw [← hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun l _ _ => hF l)

/-- Each actual finite prime-birth factor has the literal source exponential
bound, uniform in the pending cutoff. -/
theorem markedRawGhostBirthFactor_sum_le_exp {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {qStage ρ v₀ : ℝ}
    (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀) (j : J) (B : ℕ) :
    (∑ l : Fin (B+1), markedRawGhostBirthFactor ν V qStage ρ v₀ j l) ≤
      Real.exp ((v₀*(1-qStage)*V j/ρ)*(∑ p : P j, ν j p)) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact markedRawGhost_group_birth_exponential _ _
    (Finset.sum_nonneg (fun p _ => hν j p))
    (div_nonneg (mul_nonneg (mul_nonneg hv₀.le (sub_nonneg.mpr hq₁)) (hV j)) hρ.le) B

/-- The actual total-truncated ordered birth integration has a product
exponential bound, with no factor from its degree or the number of choices. -/
theorem markedRawGhost_birth_cap_exponential {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {qStage ρ v₀ : ℝ}
    (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    {B : ℕ} (m : MarkedRawMemory P B) (del : MarkedRawGhostDeletion m) :
    (∑ l : MarkedRawGhostBirthSizes m del,
      ∏ j, markedRawGhostBirthFactor ν V qStage ρ v₀ j (l.1 j : ℕ)) ≤
      ∏ j, Real.exp ((v₀*(1-qStage)*V j/ρ)*(∑ p : P j, ν j p)) := by
  classical
  calc
    _ ≤ ∑ l : J → Fin (B+1), ∏ j, markedRawGhostBirthFactor ν V qStage ρ v₀ j (l j : ℕ) :=
      markedRawGhost_birth_cap_sum_le m del _ (fun l => Finset.prod_nonneg
        (fun j _ => markedRawGhostBirthFactor_nonneg ν hν V hV hq₁ hρ hv₀ j _))
    _ = ∏ j, ∑ l : Fin (B+1), markedRawGhostBirthFactor ν V qStage ρ v₀ j l :=
      (Fintype.prod_sum (fun j (l : Fin (B+1)) => markedRawGhostBirthFactor ν V qStage ρ v₀ j l)).symm
    _ ≤ _ := Finset.prod_le_prod₀
      (fun j _ => Finset.sum_nonneg (fun l _ => markedRawGhostBirthFactor_nonneg ν hν V hV hq₁ hρ hv₀ j _))
      (fun j _ => markedRawGhostBirthFactor_sum_le_exp ν hν V hV hq₁ hρ hv₀ j B)

end ArtinMatthews
