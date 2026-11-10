module

public import ArtinMatthews.MarkedMinorArcDirtyGoodRow
public import Mathlib.CategoryTheory.Category.Basic
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeCoreCount
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFiniteSums
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The source-omission/index/position gate is bounded by the literal
counted-choice mass, via a true injective finite coding. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyRawCoreGate {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (ρ : ℝ)
    (o : J → Fin M) (k : Fin (memory.1.1 jstar:ℕ)) (v : V) (t : MarkedRawPromotionTuple memory I) : ℝ := by
  classical
  exact if k ∈ markedRawDirtyDistinguishedIndices source memory jstar ∧
      ((o,markedRawPromotionTuplePrimeProduct memory I t),v) ∈ markedRawDirtyTargetChoices source
        (memory.2 jstar k) (markedRawPromotionProductSupport memory I) V hV z T Q then
    markedRawPromotionTupleDamping memory I v.1 (hV _ v.2) ρ (fun _ => 0) t else 0

theorem markedDirtyRawCoreGate_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (o : J → Fin M) (k : Fin (memory.1.1 jstar:ℕ))
    (v : V) (t : MarkedRawPromotionTuple memory I) :
    0 ≤ markedDirtyRawCoreGate source memory jstar I V hV z T Q ρ o k v t := by
  classical
  unfold markedDirtyRawCoreGate
  split_ifs
  · exact markedRawPromotionTupleDamping_nonneg memory I v.1 (hV _ v.2) hρ (fun _ => 0) t
  · exact le_rfl

theorem markedDirtyRawCoreGate_sum_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} (source : MarkedRawActive P M)
    (memory : MarkedRawMemory P B) (jstar : J) (I : Finset J)
    (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2) (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∑ o : J → Fin M, ∑ k : Fin (memory.1.1 jstar:ℕ), ∑ v : V,
      ∑ t : MarkedRawPromotionTuple memory I, markedUniformOmissionWeight M o*
        markedDirtyRawCoreGate source memory jstar I V hV z T Q ρ o k v t) ≤
      markedRawDirtyGoodChoiceMass source memory jstar I V hV z T Q ρ (fun _ _ _ => 0) := by
  classical
  let X := ((J → Fin M) × Fin (memory.1.1 jstar:ℕ)) × (V × MarkedRawPromotionTuple memory I)
  let S : Finset X := Finset.univ.filter (fun x =>
    x.1.2 ∈ markedRawDirtyDistinguishedIndices source memory jstar ∧
    ((x.1.1,markedRawPromotionTuplePrimeProduct memory I x.2.2),x.2.1) ∈
      markedRawDirtyTargetChoices source (memory.2 jstar x.1.2)
        (markedRawPromotionProductSupport memory I) V hV z T Q)
  let encode : S → MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q := fun x =>
    ⟨⟨x.1.1.2,(Finset.mem_filter.mp x.2).2.1⟩,
      ⟨⟨((x.1.1.1,markedRawPromotionTuplePrimeProduct memory I x.1.2.2),x.1.2.1),
        (Finset.mem_filter.mp x.2).2.2⟩,⟨x.1.2.2,rfl⟩⟩⟩
  let decode : MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q → X := fun c =>
    ((c.2.1.1.1.1,c.1.1),(c.2.1.1.2,c.2.2.1))
  have hinj : Function.Injective encode := by
    intro a b hab
    exact Subtype.ext (congrArg decode hab)
  have hweight : ∀ c : MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q,
      0 ≤ markedDirtyRawCountedWeight source memory jstar I V hV z T Q ρ c := by
    intro c
    apply mul_nonneg
    · rw [markedUniformOmissionWeight_eq]
      positivity
    · exact markedRawPromotionTupleDamping_nonneg memory I _ _ hρ (fun _ => 0) _
  calc
    _ = ∑ x : X, markedUniformOmissionWeight M x.1.1*
        markedDirtyRawCoreGate source memory jstar I V hV z T Q ρ x.1.1 x.1.2 x.2.1 x.2.2 := by
      simp only [X,Fintype.sum_prod_type]
    _ = ∑ x ∈ S, markedUniformOmissionWeight M x.1.1*
        markedRawPromotionTupleDamping memory I x.2.1.1 (hV _ x.2.1.2) ρ (fun _ => 0) x.2.2 := by
      simp only [S,Finset.sum_filter,markedDirtyRawCoreGate,mul_ite,mul_zero]
    _ = ∑ x : S, markedUniformOmissionWeight M x.1.1.1*
        markedRawPromotionTupleDamping memory I x.1.2.1.1 (hV _ x.1.2.1.2) ρ (fun _ => 0) x.1.2.2 :=
      (Finset.sum_coe_sort S _).symm
    _ ≤ ∑ c : MarkedDirtyRawCountedChoice source memory jstar I V hV z T Q,
        markedDirtyRawCountedWeight source memory jstar I V hV z T Q ρ c :=
      markedDirtyFinite_sum_le_of_injective encode hinj _ _ hweight (fun _ => le_rfl)
    _ = _ := markedDirtyRawCountedWeight_sum source memory jstar I V hV z T Q ρ

end ArtinMatthews
