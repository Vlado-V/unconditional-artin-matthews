module

public import ArtinMatthews.MarkedMemoryPrimeLifespanChoices
public import Mathlib.Analysis.Complex.Exponential
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Bounds for the literal strict orphan choices. Their nonnegative
mass and exponential marking use the actual damping products, with
eta in the unit interval; incompatible choices continue to have weight
zero. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} [DecidableEq L]
  (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)
  (heta : ∀ v,0≤eta v ∧ eta v≤1)

include heta in
theorem markedMemoryOrphanDamping_bounds (v : Fin (N+1)) (a : L) :
    0≤1-eta v*markedLineHit line v a ∧ 1-eta v*markedLineHit line v a≤1 := by
  unfold markedLineHit
  split_ifs <;> simp only [mul_one,mul_zero,sub_zero]
  · constructor <;> linarith [(heta v).1,(heta v).2]
  · constructor <;> norm_num

include heta in
theorem markedMemoryOrphanInterval_bounds (a b : Fin (N+1)) :
    0≤(if line a=line b then eta a*eta b*
      ∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
        (1-eta v*markedLineHit line v (line a)) else 0) ∧
    (if line a=line b then eta a*eta b*
      ∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
        (1-eta v*markedLineHit line v (line a)) else 0)≤1 := by
  have hp0 : 0≤∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
      (1-eta v*markedLineHit line v (line a)) :=
    Finset.prod_nonneg (fun v _ => (markedMemoryOrphanDamping_bounds eta line heta v (line a)).1)
  have hp1 : (∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
      (1-eta v*markedLineHit line v (line a)))≤1 :=
    Finset.prod_le_one₀
      (fun v _ => (markedMemoryOrphanDamping_bounds eta line heta v (line a)).1)
      (fun v _ => (markedMemoryOrphanDamping_bounds eta line heta v (line a)).2)
  have hab0 : 0≤eta a*eta b := mul_nonneg (heta a).1 (heta b).1
  have hab1 : eta a*eta b≤1 := by nlinarith [(heta a).1,(heta a).2,(heta b).1,(heta b).2]
  split_ifs
  · exact ⟨mul_nonneg hab0 hp0,(mul_le_mul_of_nonneg_left hp1 hab0).trans (by simpa using hab1)⟩
  · exact ⟨le_rfl,zero_le_one⟩

include heta in
theorem markedMemoryOrphanGhostSum_bounds :
    0 ≤ markedMemoryOrphanGhostSum eta line ∧
      markedMemoryOrphanGhostSum eta line ≤ ((N:ℝ)+1)^2 := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      (markedMemoryOrphanInterval_bounds eta line heta a b).1))
  · unfold markedMemoryOrphanGhostSum
    calc
      _ ≤ ∑ _a : Fin (N+1),((N:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro a _
        calc
          _ ≤ ∑ _b∈Finset.univ.filter (fun b : Fin (N+1) => a<b),(1:ℝ) :=
            Finset.sum_le_sum (fun b _ => (markedMemoryOrphanInterval_bounds eta line heta a b).2)
          _ = ((Finset.univ.filter (fun b : Fin (N+1) => a<b)).card:ℝ) := by simp
          _ ≤ (N:ℝ)+1 := by
            have hc : (Finset.univ.filter (fun b : Fin (N+1) => a<b)).card≤N+1 := by
              simpa only [Fintype.card_fin] using Finset.card_le_univ (Finset.univ.filter (fun b : Fin (N+1) => a<b))
            exact_mod_cast hc
      _ = ((N:ℝ)+1)^2 := by simp; ring

include heta in
theorem markedMemoryOrphanChoice_nonneg (atom : ℝ) (ha : 0≤atom)
    (c : MarkedMemoryPrimeLifespanChoice N) :
    0 ≤ markedMemoryOrphanChoice eta line atom c := by
  rcases c with ⟨a,b⟩
  cases a with
  | none => cases b <;> norm_num [markedMemoryOrphanChoice]
  | some a =>
    cases b with
    | none => exact le_rfl
    | some b =>
      change 0≤(if a<b then atom*(if line a=line b then eta a*eta b*
        ∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
          (1-eta v*markedLineHit line v (line a)) else 0) else 0)
      by_cases hab : a<b
      · simp only [hab,ite_true]
        exact mul_nonneg ha (markedMemoryOrphanInterval_bounds eta line heta a b).1
      · simp only [hab,ite_false,le_refl]

def markedMemoryOrphanChoiceCost (c : MarkedMemoryPrimeLifespanChoice N) : ℕ :=
  if c=(none,none) then 0 else 1

theorem markedMemoryOrphanChoice_generating (atom r : ℝ) :
    (∑ c : MarkedMemoryPrimeLifespanChoice N,
      r ^ markedMemoryOrphanChoiceCost c * markedMemoryOrphanChoice eta line atom c) =
      1+r*(atom*markedMemoryOrphanGhostSum eta line) := by
  have he (c : MarkedMemoryPrimeLifespanChoice N) :
      r ^ markedMemoryOrphanChoiceCost c * markedMemoryOrphanChoice eta line atom c =
      r*markedMemoryOrphanChoice eta line atom c + (if c=(none,none) then 1-r else 0) := by
    by_cases hc : c=(none,none)
    · subst c
      simp only [markedMemoryOrphanChoiceCost,ite_true,pow_zero,markedMemoryOrphanChoice,mul_one]
      ring
    · simp only [markedMemoryOrphanChoiceCost,hc,ite_false,pow_one,add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,markedMemoryOrphanChoice_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

include heta in
theorem markedMemoryOrphanChoice_generating_le_exp (atom r : ℝ) (ha : 0≤atom) (hr : 0≤r) :
    (∑ c : MarkedMemoryPrimeLifespanChoice N,
      r ^ markedMemoryOrphanChoiceCost c * markedMemoryOrphanChoice eta line atom c) ≤
      Real.exp (r*atom*((N:ℝ)+1)^2) := by
  rw [markedMemoryOrphanChoice_generating]
  calc
    _ ≤ 1+r*atom*((N:ℝ)+1)^2 := by
      have h := mul_le_mul_of_nonneg_left (markedMemoryOrphanGhostSum_bounds eta line heta).2 (mul_nonneg hr ha)
      nlinarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (r*atom*((N:ℝ)+1)^2)

end
end ArtinMatthews
