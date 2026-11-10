module

public import ArtinMatthews.MarkedMinorArcDirtyPromotionChoices
public import ArtinMatthews.MarkedMinorArcDirtyTargetChoices
public import ArtinMatthews.MarkedMinorArcDirtyTargetCount
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

/-! The literal fixed-good-draw dirty choice row, including actual repeated
pending-index promotions and exact uniform source omissions. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedRawDirtyDistinguishedIndices {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) : Finset (Fin (memory.1.1 jstar:ℕ)) := by
  classical
  exact Finset.univ.filter (fun k => ∀ j l, (source j l).1 ≠ (memory.2 jstar k).1.1)

def markedRawPromotionProductSupport {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (memory : MarkedRawMemory P B) (I : Finset J) : Finset ℕ := by
  classical
  exact Finset.univ.image (markedRawPromotionTuplePrimeProduct memory I)

def markedRawDirtyGoodChoiceMass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ)
    (ρ : ℝ) (newHits : (J → Fin M) → V → I → ℕ) : ℝ := by
  classical
  exact ∑ k ∈ markedRawDirtyDistinguishedIndices source memory jstar,
    ∑ c ∈ markedRawDirtyTargetChoices source (memory.2 jstar k)
      (markedRawPromotionProductSupport memory I) V hV z T Q,
      markedUniformOmissionWeight M c.1.1 *
        ∑ t ∈ Finset.univ.filter (fun t : MarkedRawPromotionTuple memory I =>
          markedRawPromotionTuplePrimeProduct memory I t=c.1.2),
          markedRawPromotionTupleDamping memory I c.2.1 (hV _ c.2.2) ρ (newHits c.1.1 c.2) t

theorem markedRawDirtyGoodChoiceMass_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hdist : ∀ j, Function.Injective (source j))
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hp : ∀ k ∈ markedRawDirtyDistinguishedIndices source memory jstar,
      1/((memory.2 jstar k).1.1:ℕ) ≤ ε)
    (hg : ((markedMinorIntegerTau r w/markedMinorIntegerTau r z:ℝ):AddCircle (1:ℝ)) ∉
      markedPairBadRoots Q T (100*ε)) (newHits : (J → Fin M) → V → I → ℕ) :
    markedRawDirtyGoodChoiceMass source memory jstar I V hV z T Q ρ newHits ≤
      33*(B:ℝ)*(M:ℝ)⁻¹^(Fintype.card J)*(1/(1-ρ)^2)^(I.card) := by
  classical
  let C : ℝ := (1/(1-ρ)^2)^(I.card)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let H := markedRawDirtyDistinguishedIndices source memory jstar
  have hH : H.card ≤ B := by
    calc
      _ ≤ (Finset.univ : Finset (Fin (memory.1.1 jstar:ℕ))).card := Finset.card_filter_le _ _
      _ = (memory.1.1 jstar:ℕ) := by simp
      _ ≤ B := markedRawMemory_group_size_le memory jstar
  have hweight (o : J → Fin M) : 0 ≤ markedUniformOmissionWeight M o := by
    rw [markedUniformOmissionWeight_eq]
    positivity
  have hpoint (k) (hk : k ∈ H) :
      (∑ c ∈ markedRawDirtyTargetChoices source (memory.2 jstar k)
        (markedRawPromotionProductSupport memory I) V hV z T Q,
        markedUniformOmissionWeight M c.1.1 *
          ∑ t ∈ Finset.univ.filter (fun t : MarkedRawPromotionTuple memory I =>
            markedRawPromotionTuplePrimeProduct memory I t=c.1.2),
            markedRawPromotionTupleDamping memory I c.2.1 (hV _ c.2.2) ρ (newHits c.1.1 c.2) t) ≤
        (33*(M:ℝ)⁻¹^(Fintype.card J))*C := by
    calc
      _ ≤ ∑ c ∈ markedRawDirtyTargetChoices source (memory.2 jstar k)
          (markedRawPromotionProductSupport memory I) V hV z T Q,
          markedUniformOmissionWeight M c.1.1*C := by
        apply Finset.sum_le_sum
        intro c _
        exact mul_le_mul_of_nonneg_left (markedRawPromotionTupleDamping_product_fiber_le
          memory I c.2.1 (hV _ c.2.2) hρ₀ hρ₁ (newHits c.1.1 c.2) c.1.2) (hweight _)
      _ = (∑ c ∈ markedRawDirtyTargetChoices source (memory.2 jstar k)
          (markedRawPromotionProductSupport memory I) V hV z T Q,
          markedUniformOmissionWeight M c.1.1)*C := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (markedRawDirtyTargetChoices_weight_le source hdis hdist (memory.2 jstar k)
          (Finset.mem_filter.mp hk).2 (markedRawPromotionProductSupport memory I) V hV z w T Q r
          hd hz hbox hε (hp k hk) hg) hC
  calc
    _ ≤ ∑ _k ∈ H, (33*(M:ℝ)⁻¹^(Fintype.card J))*C := Finset.sum_le_sum (fun k hk => hpoint k hk)
    _ = (H.card:ℝ)*((33*(M:ℝ)⁻¹^(Fintype.card J))*C) := by simp
    _ ≤ (B:ℝ)*((33*(M:ℝ)⁻¹^(Fintype.card J))*C) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hH) (by positivity)
    _ = _ := by dsimp [C]; ring

end ArtinMatthews
