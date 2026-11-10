module

public import ArtinMatthews.MarkedSparsePrimeMoments
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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

/-! The actual finite family of unit intervals meeting a large-value set,
and the uniform elementary norm bound for the prime-label polynomial. -/
namespace ArtinMatthews
open Finset Filter
open scoped Topology

noncomputable def markedExceptionalUnitIntervals (P : ℝ → ℂ) (T ε : ℝ) : Finset ℤ := by
  classical
  exact (Icc ⌊-T⌋ ⌊T⌋).filter (fun z => ∃ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1),
    |t| ≤ T ∧ ε ≤ ‖P t‖)

lemma markedExceptionalUnitIntervals_witness (P : ℝ → ℂ) (T ε : ℝ) :
    ∀ z ∈ markedExceptionalUnitIntervals P T ε,
      ∃ t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1), |t| ≤ T ∧ ε ≤ ‖P t‖ := by
  classical
  intro z hz
  exact (mem_filter.mp hz).2

lemma markedExceptionalUnitIntervals_cover (P : ℝ → ℂ) (T ε : ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc (-T) T) (hP : ε ≤ ‖P t‖) :
    ∃ z ∈ markedExceptionalUnitIntervals P T ε, t ∈ Set.Icc (z:ℝ) ((z:ℝ)+1) := by
  classical
  have hunit : t ∈ Set.Icc (⌊t⌋:ℝ) ((⌊t⌋:ℝ)+1) :=
    ⟨Int.floor_le t,(Int.lt_floor_add_one t).le⟩
  refine ⟨⌊t⌋,mem_filter.mpr ⟨mem_Icc.mpr
    ⟨Int.floor_mono ht.1,Int.floor_mono ht.2⟩,?_⟩,hunit⟩
  exact ⟨t,hunit,abs_le.mpr ht,hP⟩

lemma markedPrimePolynomial_continuous {k : ℕ} (P : Finset ℕ) (Y : ℝ)
    (χ : DirichletCharacter ℂ k) (ξ : ℝ) :
    Continuous (markedPrimePolynomial P Y χ ξ) := by
  unfold markedPrimePolynomial markedPrimePhase
  fun_prop

 theorem markedPrimePolynomial_norm_le_two {k : ℕ} (P : Finset ℕ) {Y : ℝ}
    (hY : 0 < Y) (χ : DirichletCharacter ℂ k) (ξ t : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hcap : ∀ p ∈ P, (p:ℝ) ≤ 2*Y) :
    ‖markedPrimePolynomial P Y χ ξ t‖ ≤ 2 := by
  have hc : (P.card:ℝ) ≤ 2*Y := by
    have hsub : P ⊆ Ioc 0 ⌊2*Y⌋₊ := by
      intro p hp
      exact mem_Ioc.mpr ⟨(hP p hp).pos,(Nat.le_floor_iff (by positivity)).mpr (hcap p hp)⟩
    have hh : (P.card:ℝ) ≤ (⌊2*Y⌋₊:ℝ) := by
      exact_mod_cast (card_le_card hsub).trans_eq (by simp)
    exact hh.trans (Nat.floor_le (by positivity))
  unfold markedPrimePolynomial
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY]
  apply (div_le_iff₀ hY).mpr
  calc
    _ ≤ ∑ p ∈ P, ‖χ p*markedPrimePhase p (t+ξ)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ P, (1:ℝ) := by
      apply sum_le_sum
      intro p _
      rw [norm_mul,markedPrimePhase_norm,mul_one]
      exact DirichletCharacter.norm_le_one χ p
    _ = (P.card:ℝ) := by simp
    _ ≤ _ := hc

end ArtinMatthews
