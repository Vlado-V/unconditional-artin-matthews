module

public import ArtinMatthews.MarkedMinorArcRawGhostAction
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

/-! Literal positive Schur weight for the actual total-truncated memory,
and exact weight ratios for indexed ghost deletion and anchored birth. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Source Schur weight v₀ to the true total pending degree. -/
def markedRawMemorySchurWeight {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (v₀ : ℝ) (m : MarkedRawMemory P B) : ℝ :=
  v₀^(∑ j, (m.1.1 j : ℕ))

theorem markedRawMemorySchurWeight_pos {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} {v₀ : ℝ} (hv₀ : 0 < v₀) (m : MarkedRawMemory P B) :
    0 < markedRawMemorySchurWeight v₀ m := pow_pos hv₀ _

theorem markedRawMemorySchurWeight_prod {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (v₀ : ℝ) (m : MarkedRawMemory P B) :
    markedRawMemorySchurWeight v₀ m=∏ j, v₀^(m.1.1 j : ℕ) :=
  (Finset.prod_pow_eq_pow_sum Finset.univ _ _).symm

/-- Every literal old deletion mask partitions its actual indexed list. -/
theorem markedRawGhostSurvivors_card_add {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (del : MarkedRawGhostDeletion m) (j : J) :
    (markedRawGhostSurvivors m del j).card+(del j).card=(m.1.1 j : ℕ) := by
  have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (del j))
  simpa only [markedRawGhostSurvivors,Finset.card_univ,Fintype.card_fin] using hh

/-- Exact source Schur-weight ratio of the actual ghost target. There is
one v₀ per ordered birth and one v₀^-1 per indexed old deletion, with no
factor from the number of groups, sizes, primes, or projective anchors. -/
theorem markedRawGhost_target_weight_ratio {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} {v₀ : ℝ} (hv₀ : v₀ ≠ 0)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) :
    markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
      markedRawMemorySchurWeight v₀ m=∏ j, v₀^(l.1 j : ℕ)/v₀^(del j).card := by
  rw [markedRawMemorySchurWeight_prod,markedRawMemorySchurWeight_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  change v₀^((markedRawGhostSurvivors m del j).card+(l.1 j : ℕ))/v₀^(m.1.1 j : ℕ)=_
  have he : v₀^(m.1.1 j : ℕ)=v₀^((markedRawGhostSurvivors m del j).card+(del j).card) :=
    congrArg (fun k : ℕ => v₀^k) (markedRawGhostSurvivors_card_add m del j).symm
  rw [he,pow_add,pow_add]
  field_simp [pow_ne_zero _ hv₀]

/-- The true absolute ghost-choice weighted row, before deriving bounds.
It sums exactly the literal actual masks, admissible total sizes and births. -/
noncomputable def markedRawGhostWeightedAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ v₀ : ℝ)
    {B : ℕ} (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : ℝ := by
  classical
  exact ∑ del : MarkedRawGhostDeletion m,
    if MarkedRawGhostDeletionAllowed m z hz del then
      ∑ l : MarkedRawGhostBirthSizes m del, ∑ births : MarkedRawGhostBirthLabels l,
        |markedRawGhostSignedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births| *
          (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
            markedRawMemorySchurWeight v₀ m)
    else 0

end ArtinMatthews
