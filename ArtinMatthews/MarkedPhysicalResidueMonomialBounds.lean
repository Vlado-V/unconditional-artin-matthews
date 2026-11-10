module

public import ArtinMatthews.MarkedPhysicalBonferroniResidue
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

/-! Every true selected-residue damping monomial lies in [0,1]. This
discharges the fixed residue coefficient in weighted root replacement. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalResidueVisitFactor_mem_unitInterval {S : ℕ} (hS : Squarefree S)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (active : Finset ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (p : ℕ) :
    0 ≤ markedPhysicalResidueVisitFactor hS g active r z hz p ∧
      markedPhysicalResidueVisitFactor hS g active r z hz p ≤ 1 := by
  unfold markedPhysicalResidueVisitFactor
  split_ifs <;> constructor <;> linarith

theorem markedPhysicalResiduePrimePathFactor_mem_unitInterval
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (hS : Squarefree S) (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (p : ℕ) :
    0 ≤ markedPhysicalResiduePrimePathFactor hS g I a r z hz p ∧
      markedPhysicalResiduePrimePathFactor hS g I a r z hz p ≤ 1 := by
  have hf (v : ι) (hv : v ∈ I) := markedPhysicalResidueVisitFactor_mem_unitInterval hS g
    (markedPhysicalActivePrimes (a v)) (hr v hv).1 (hr v hv).2 (z v) (hz v) p
  exact ⟨Finset.prod_nonneg (fun v hv => (hf v hv).1),
    Finset.prod_le_one₀ (fun v hv => (hf v hv).1) (fun v hv => (hf v hv).2)⟩

theorem markedPhysicalResidueBonferroniMonomial_mem_unitInterval
    {J ι : Type*} [Fintype J] {P : J → Finset ℕ} {M S : ℕ}
    (hS : Squarefree S) (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (I : Finset ι) (a : ι → MarkedPhysicalMarking P M) (r : ι → ℝ)
    (hr : ∀ v ∈ I,0 ≤ r v ∧ r v ≤ 1)
    (z : ι → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (T : Finset ℕ) :
    0 ≤ markedPhysicalResidueBonferroniMonomial hS g I a r z hz T ∧
      markedPhysicalResidueBonferroniMonomial hS g I a r z hz T ≤ 1 := by
  have hf (p : ℕ) := markedPhysicalResiduePrimePathFactor_mem_unitInterval hS g I a r hr z hz p
  have hx (p : ℕ) : 0 ≤ markedPhysicalResiduePrimeLoss hS g I a r z hz p ∧
      markedPhysicalResiduePrimeLoss hS g I a r z hz p ≤ 1 := by
    have hh := hf p
    exact ⟨sub_nonneg.mpr hh.2,by unfold markedPhysicalResiduePrimeLoss; linarith⟩
  have hu0 : 0 ≤ ∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalResiduePrimePathFactor hS g I a r z hz p :=
    Finset.prod_nonneg (fun p _ => (hf p).1)
  have hu1 : (∏ p ∈ markedPhysicalPathUsedPrimes I a,markedPhysicalResiduePrimePathFactor hS g I a r z hz p) ≤ 1 :=
    Finset.prod_le_one₀ (fun p _ => (hf p).1) (fun p _ => (hf p).2)
  have ht0 : 0 ≤ ∏ p ∈ T,markedPhysicalResiduePrimeLoss hS g I a r z hz p :=
    Finset.prod_nonneg (fun p _ => (hx p).1)
  have ht1 : (∏ p ∈ T,markedPhysicalResiduePrimeLoss hS g I a r z hz p) ≤ 1 :=
    Finset.prod_le_one₀ (fun p _ => (hx p).1) (fun p _ => (hx p).2)
  exact ⟨mul_nonneg hu0 ht0,(mul_le_mul hu1 ht1 ht0 zero_le_one).trans_eq (one_mul _)⟩

end ArtinMatthews
