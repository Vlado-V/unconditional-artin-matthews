module

public import ArtinMatthews.MarkedMinorArcRawGhostWeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual signed ghost coefficients under the positive pending Schur
weight. Signs are removed by absolute values only in this estimate, while
the target state and its exact birth/deletion weight ratio are retained. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The literal one-group absolute weighted factor of a ghost choice. -/
noncomputable def markedRawGhostAbsoluteFactor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage ρ v₀ : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) (j : J) : ℝ :=
  ((1-qStage)/(ρ*v₀))^(del j).card*
    (qStage/ρ^2)^((markedRawGroupHitIndices m j z hz \ del j).card)*
    (v₀*(1-qStage)*V j/ρ)^(l.1 j : ℕ)

/-- Exact absolute signed coefficient times the actual source weight ratio,
including every repeated old index and every ordered birth. -/
theorem markedRawGhost_signed_absolute_weight {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {qStage ρ v₀ : ℝ} (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) :
    |markedRawGhostSignedCoefficient V qStage ρ m z hz del l| *
      (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
        markedRawMemorySchurWeight v₀ m)=
      ∏ j, markedRawGhostAbsoluteFactor V qStage ρ v₀ m z hz del l j := by
  rw [markedRawGhost_target_weight_ratio hv₀.ne',markedRawGhostSignedCoefficient,Finset.abs_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hη : 0 ≤ 1-qStage := sub_nonneg.mpr hq₁
  have hd : |-(1-qStage)/ρ|=(1-qStage)/ρ := by
    rw [abs_div,abs_neg,abs_of_nonneg hη,abs_of_pos hρ]
  have hs : |qStage/ρ^2|=qStage/ρ^2 := abs_of_nonneg (div_nonneg hq₀ (sq_nonneg _))
  have hb : |-(1-qStage)*V j/ρ|=(1-qStage)*V j/ρ := by
    rw [show -(1-qStage)*V j/ρ=-((1-qStage)*V j/ρ) by ring,abs_neg,
      abs_of_nonneg (div_nonneg (mul_nonneg hη (hV j)) hρ.le)]
  rw [abs_mul,abs_mul,abs_pow,hd,abs_pow,hs,abs_pow,hb]
  unfold markedRawGhostAbsoluteFactor
  simp only [div_pow,mul_pow]
  field_simp [pow_ne_zero _ hρ.ne',pow_ne_zero _ hv₀.ne']

/-- The literal choice coefficient, prime birth mass and target Schur ratio
factor exactly into nonnegative actual birth integration and group factors. -/
theorem markedRawGhost_choice_absolute_weight {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    {B : ℕ} (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {qStage ρ v₀ : ℝ} (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del)
    (births : MarkedRawGhostBirthLabels l) :
    |markedRawGhostSignedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births| *
      (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
        markedRawMemorySchurWeight v₀ m)=
      markedRawGhostBirthMass ν l births*
        ∏ j, markedRawGhostAbsoluteFactor V qStage ρ v₀ m z hz del l j := by
  rw [abs_mul,abs_of_nonneg (markedRawGhostBirthMass_nonneg ν hν l births)]
  rw [mul_right_comm _ (markedRawGhostBirthMass ν l births)]
  rw [markedRawGhost_signed_absolute_weight V hV hq₀ hq₁ hρ hv₀]
  ring

end ArtinMatthews
