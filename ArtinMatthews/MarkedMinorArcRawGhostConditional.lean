module

public import ArtinMatthews.MarkedMinorArcRawGhostWeight
public import ArtinMatthews.MarkedMinorArcRawGhostDeletionRow
public import ArtinMatthews.MarkedMinorArcRawGhostFullRow
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Conditional birth constraints in the literal ghost row. The input
is a bound on the actual ordered tuple integral at each fixed length;
no independence between the prescribed primes is required. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawGhostConditionalWeightedAbsRow {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ v₀ : ℝ) {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (gate : (del : MarkedRawGhostDeletion m) → (l : MarkedRawGhostBirthSizes m del) →
      MarkedRawGhostBirthLabels l → Prop) : ℝ :=
  ∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
    ∑ l : MarkedRawGhostBirthSizes m del, ∑ births : MarkedRawGhostBirthLabels l,
      if gate del l births then
        |markedRawGhostSignedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births| *
          (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
            markedRawMemorySchurWeight v₀ m)
      else 0
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhost_conditional_weighted_row
    {J : Type*} [Fintype J] [decJ : DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) {qStage ρ v₀ D N : ℝ}
    (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ) (hv₀ : 0 < v₀)
    (hD : 0 ≤ D) (hN : 0 ≤ N) {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (gate : (del : MarkedRawGhostDeletion m) → (l : MarkedRawGhostBirthSizes m del) →
      MarkedRawGhostBirthLabels l → Prop)
    (hmass : ∀ del l, (∑ births : MarkedRawGhostBirthLabels l,
        if gate del l births then markedRawGhostBirthMass ν l births else 0) ≤
      D*∏ j, N^(l.1 j:ℕ)/(Nat.factorial (l.1 j:ℕ):ℝ)) :
    markedRawGhostConditionalWeightedAbsRow ν V qStage ρ v₀ m z hz gate ≤
      D*(∏ j, Real.exp ((v₀*(1-qStage)*V j/ρ)*N))*
        ∏ j, (qStage/ρ^2+(1-qStage)/(ρ*v₀))^(markedRawGroupHitIndices m j z hz).card := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let c := fun j => v₀*(1-qStage)*V j/ρ
  let F (j : J) (l : Fin (B+1)) := (c j)^l.1*N^l.1/(Nat.factorial l.1:ℝ)
  have hc (j : J) : 0 ≤ c j :=
    div_nonneg (mul_nonneg (mul_nonneg hv₀.le (sub_nonneg.mpr hq₁)) (hV j)) hρ.le
  have hF (j : J) (l : Fin (B+1)) : 0 ≤ F j l := by
    exact div_nonneg (mul_nonneg (pow_nonneg (hc j) _) (pow_nonneg hN _)) (Nat.cast_nonneg _)
  have hbirth (del : MarkedRawGhostDeletion m) :
      (∑ l : MarkedRawGhostBirthSizes m del, ∏ j, F j (l.1 j)) ≤
        ∏ j, Real.exp (c j*N) := by
    calc
      _ ≤ ∑ l : J → Fin (B+1), ∏ j, F j (l j) :=
        markedRawGhost_birth_cap_sum_le m del _ (fun l => Finset.prod_nonneg (fun j _ => hF j (l j)))
      _ = ∏ j, ∑ l : Fin (B+1), F j l := (Fintype.prod_sum F).symm
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg (fun l _ => hF j l))
        intro j _
        dsimp [F]
        rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => (c j)^l*N^l/(Nat.factorial l:ℝ)) (B+1)]
        exact markedRawGhost_group_birth_exponential N (c j) hN (hc j) B
  have hpoint (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) :
      (∑ births : MarkedRawGhostBirthLabels l,
        if gate del l births then
          |markedRawGhostSignedCoefficient V qStage ρ m z hz del l*markedRawGhostBirthMass ν l births| *
            (markedRawMemorySchurWeight v₀ (markedRawGhostTargetMemory m z hz del l births)/
              markedRawMemorySchurWeight v₀ m) else 0) ≤
      D*(∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j)*∏ j, F j (l.1 j) := by
    have hA : 0 ≤ ∏ j, markedRawGhostAbsoluteFactor V qStage ρ v₀ m z hz del l j := by
      apply Finset.prod_nonneg
      intro j _
      unfold markedRawGhostAbsoluteFactor
      exact mul_nonneg
        (mul_nonneg
          (pow_nonneg (div_nonneg (sub_nonneg.mpr hq₁) (mul_pos hρ hv₀).le) _)
          (pow_nonneg (div_nonneg hq₀ (sq_nonneg _)) _)) (pow_nonneg (hc j) _)
    calc
      _ = (∑ births : MarkedRawGhostBirthLabels l,
          if gate del l births then markedRawGhostBirthMass ν l births else 0)*
          ∏ j, markedRawGhostAbsoluteFactor V qStage ρ v₀ m z hz del l j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro births _
        split_ifs
        · exact markedRawGhost_choice_absolute_weight ν hν V hV hq₀ hq₁ hρ hv₀ m z hz del l births
        · simp only [zero_mul]
      _ ≤ (D*∏ j, N^(l.1 j:ℕ)/(Nat.factorial (l.1 j:ℕ):ℝ))*
          ∏ j, markedRawGhostAbsoluteFactor V qStage ρ v₀ m z hz del l j :=
        mul_le_mul_of_nonneg_right (hmass del l) hA
      _ = _ := by
        rw [mul_assoc,mul_assoc,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro j _
        dsimp [F,c,markedRawGhostAbsoluteFactor,markedRawGhostDeletionFactor]
        ring
  unfold markedRawGhostConditionalWeightedAbsRow
  calc
    _ ≤ ∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
        ∑ l : MarkedRawGhostBirthSizes m del,
          D*(∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j)*∏ j, F j (l.1 j)
        else 0 := by
      apply Finset.sum_le_sum
      intro del _
      split_ifs
      · exact Finset.sum_le_sum (fun l _ => hpoint del l)
      · exact le_rfl
    _ ≤ ∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
        D*(∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j)*
          ∏ j, Real.exp (c j*N) else 0 := by
      apply Finset.sum_le_sum
      intro del _
      split_ifs
      · rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hbirth del) (mul_nonneg hD (Finset.prod_nonneg
          (fun j _ => markedRawGhostDeletionFactor_nonneg hq₀ hq₁ hρ hv₀ m z hz del j)))
      · exact le_rfl
    _ = _ := by
      have heq : (∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
          D*(∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j)*
            ∏ j, Real.exp (c j*N) else 0) =
          D*(∑ del : MarkedRawGhostDeletion m, if MarkedRawGhostDeletionAllowed m z hz del then
            ∏ j, markedRawGhostDeletionFactor qStage ρ v₀ m z hz del j else 0)*
              ∏ j, Real.exp (c j*N) := by
        rw [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro del _
        split_ifs <;> simp only [mul_zero,zero_mul]
      rw [heq,markedRawGhost_deletion_sum]
      dsimp [c]
      ring

end ArtinMatthews
