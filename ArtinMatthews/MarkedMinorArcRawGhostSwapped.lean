module

public import ArtinMatthews.MarkedMinorArcRawGhostWeight
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal ghost rule with deletion and anchored-birth charges swapped.
This is the explicit finite rule identified by the symmetric factorial
adjoint calculation; its operator-adjoint identification is proved separately. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Actual swapped charges: an old deletion pays -eta'*V_i/rho and an
anchored birth pays -eta'/rho, with the same surviving-hit factor. -/
noncomputable def markedRawGhostSwappedCoefficient {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage ρ : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) : ℝ :=
  ∏ j, (-(1-qStage)*V j/ρ)^(del j).card*
    (qStage/ρ^2)^((markedRawGroupHitIndices m j z hz \ del j).card)*
    (-(1-qStage)/ρ)^(l.1 j : ℕ)

/-- In the true eventual range 0≤V_i≤1, the swapped absolute coefficient is
bounded by the literal unit-V ghost coefficient. No row bound is assumed. -/
theorem markedRawGhostSwappedCoefficient_abs_le_one {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (hV₀ : ∀ j, 0 ≤ V j) (hV₁ : ∀ j, V j ≤ 1)
    (qStage ρ : ℝ) (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) :
    |markedRawGhostSwappedCoefficient V qStage ρ m z hz del l| ≤
      |markedRawGhostSignedCoefficient (fun _ => 1) qStage ρ m z hz del l| := by
  unfold markedRawGhostSwappedCoefficient markedRawGhostSignedCoefficient
  rw [Finset.abs_prod,Finset.abs_prod]
  apply Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
  intro j _
  have hd : |-(1-qStage)*V j/ρ| ≤ |-(1-qStage)/ρ| := by
    rw [show -(1-qStage)*V j/ρ=(-(1-qStage)/ρ)*V j by ring,abs_mul,abs_of_nonneg (hV₀ j)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hV₁ j)
  simp only [abs_mul,abs_pow,mul_one]
  gcongr

/-- The actual absolute weighted row of the explicitly swapped rule. -/
noncomputable def markedRawGhostSwappedWeightedAbsRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ v₀ : ℝ)
    {B : ℕ} (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : ℝ := by
  classical
  exact ∑ del : MarkedRawGhostDeletion m,
    if MarkedRawGhostDeletionAllowed m z hz del then
      ∑ l : MarkedRawGhostBirthSizes m del, ∑ births : MarkedRawGhostBirthLabels l,
        |markedRawGhostSwappedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births| *
          (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
            markedRawMemorySchurWeight v₀ m)
    else 0

/-- Exact literal row domination of the swapped rule by the unit-V ghost,
with every actual mask, truncation, birth and source Schur ratio unchanged. -/
theorem markedRawGhostSwappedWeightedAbsRow_le_one {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (hV₀ : ∀ j, 0 ≤ V j) (hV₁ : ∀ j, V j ≤ 1) (qStage ρ : ℝ)
    {v₀ : ℝ} (hv₀ : 0 < v₀) {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedRawGhostSwappedWeightedAbsRow ν V qStage ρ v₀ m z hz ≤
      markedRawGhostWeightedAbsRow ν (fun _ => 1) qStage ρ v₀ m z hz := by
  classical
  unfold markedRawGhostSwappedWeightedAbsRow markedRawGhostWeightedAbsRow
  apply Finset.sum_le_sum
  intro del _
  split_ifs
  · apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro births _
    rw [abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (markedRawGhostSwappedCoefficient_abs_le_one V hV₀ hV₁ qStage ρ m z hz del l)
        (abs_nonneg _))
      (div_nonneg (markedRawMemorySchurWeight_pos hv₀ _).le (markedRawMemorySchurWeight_pos hv₀ _).le)
  · exact le_rfl

end ArtinMatthews
