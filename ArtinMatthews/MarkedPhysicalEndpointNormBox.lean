module

public import ArtinMatthews.MarkedPhysicalEndpointNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The endpoint norm bound on the literal PD03 box
`[U,16U] × [V,2V]`, with its original physical state measure. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem markedPhysicalEndpointNorm_le_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hV : ∀ j, 0 < bandReciprocalMass (P j))
    {A B : ℕ} (hZ : ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (A : ℤ) ∧ 0 < z.2 ∧ z.2 ≤ (B : ℤ))
    (α β : ℕ → ℂ) {Cα Cβ : ℝ} (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ)
    (hα : ∀ m ∈ Finset.Ioc 0 A, ‖α m‖ ≤ Cα) (hβ : ∀ s ∈ Finset.Ioc 0 B, ‖β s‖ ≤ Cβ) :
    markedPhysicalEndpointNorm P M Z (fun j => bandReciprocalMass (P j)) α β ≤
      Real.sqrt ((A : ℝ) * B) * (Cα * Cβ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCα hCβ), ?_⟩
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  exact markedPhysicalEndpointEnergy_le_bounds P hP hdis M Z hV hZ α β hCα hCβ hα hβ

/-- The integer counting rectangle follows from the actual real box;
neither a rounding estimate nor a position-cardinality bound is assumed. -/
theorem markedPhysical_box_nat_bounds {Z : Finset (ℤ × ℤ)} {U V : ℝ}
    (hU : 0 < U) (hV : 0 < V)
    (hZ : ∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
      V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V) :
    ∀ z ∈ Z, 0 < z.1 ∧ z.1 ≤ (⌊16*U⌋₊ : ℤ) ∧
      0 < z.2 ∧ z.2 ≤ (⌊2*V⌋₊ : ℤ) := by
  intro z hz
  obtain ⟨h₁, hA, h₂, hB⟩ := hZ z hz
  have hp₁ : 0 < z.1 := by exact_mod_cast hU.trans_le h₁
  have hp₂ : 0 < z.2 := by exact_mod_cast hV.trans_le h₂
  have hn₁ : z.1.natAbs ≤ ⌊16*U⌋₊ := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 16*U)).mpr
    simpa only [Nat.cast_natAbs, abs_of_pos hp₁] using hA
  have hn₂ : z.2.natAbs ≤ ⌊2*V⌋₊ := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 2*V)).mpr
    simpa only [Nat.cast_natAbs, abs_of_pos hp₂] using hB
  refine ⟨hp₁, ?_, hp₂, ?_⟩
  · have : (z.1.natAbs : ℤ) ≤ (⌊16*U⌋₊ : ℤ) := by exact_mod_cast hn₁
    simpa only [Int.natCast_natAbs, abs_of_pos hp₁] using this
  · have : (z.2.natAbs : ℤ) ≤ (⌊2*V⌋₊ : ℤ) := by exact_mod_cast hn₂
    simpa only [Int.natCast_natAbs, abs_of_pos hp₂] using this

/-- The original beta coefficient norm sum remains exact on the literal
box. This form does not assume any pointwise beta bound. -/
theorem markedPhysicalEndpointEnergy_box_alpha {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hν : ∀ j, 0 < bandReciprocalMass (P j))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hZ : ∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
      V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V)
    (α β : ℕ → ℂ) {Cα : ℝ} (hCα : 0 ≤ Cα)
    (hα : ∀ m ∈ Finset.Ioc 0 ⌊16*U⌋₊, ‖α m‖ ≤ Cα) :
    markedPhysicalEndpointEnergy P M Z (fun j => bandReciprocalMass (P j)) α β ≤
      (16*U) * Cα ^ 2 * ∑ s ∈ Finset.Ioc 0 ⌊2*V⌋₊, ‖β s‖ ^ 2 := by
  apply (markedPhysicalEndpointEnergy_le_alpha_bound P hP hdis M Z hν
    (markedPhysical_box_nat_bounds hU hV hZ) α β hCα hα).trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity : 0 ≤ 16*U)) (sq_nonneg _)
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Genuine original physical Hilbert energy on `[U,16U] × [V,2V]`.
The absolute constant 32 is independent of K and the growing list length. -/
theorem markedPhysicalEndpointEnergy_box {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hν : ∀ j, 0 < bandReciprocalMass (P j))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hZ : ∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
      V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V)
    (α β : ℕ → ℂ) {Cα Cβ : ℝ} (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ)
    (hα : ∀ m ∈ Finset.Ioc 0 ⌊16*U⌋₊, ‖α m‖ ≤ Cα)
    (hβ : ∀ s ∈ Finset.Ioc 0 ⌊2*V⌋₊, ‖β s‖ ≤ Cβ) :
    markedPhysicalEndpointEnergy P M Z (fun j => bandReciprocalMass (P j)) α β ≤
      32*U*V*(Cα*Cβ)^2 := by
  apply (markedPhysicalEndpointEnergy_le_bounds P hP hdis M Z hν
    (markedPhysical_box_nat_bounds hU hV hZ) α β hCα hCβ hα hβ).trans
  calc
    _ ≤ (16*U)*(2*V)*(Cα*Cβ)^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (Nat.floor_le (by positivity : 0 ≤ 16*U))
          (Nat.floor_le (by positivity : 0 ≤ 2*V)) (Nat.cast_nonneg _) (by positivity))
        (sq_nonneg _)
    _ = _ := by ring

theorem markedPhysicalEndpointNorm_box {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (hν : ∀ j, 0 < bandReciprocalMass (P j))
    {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hZ : ∀ z ∈ Z, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16*U ∧
      V ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 2*V)
    (α β : ℕ → ℂ) {Cα Cβ : ℝ} (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ)
    (hα : ∀ m ∈ Finset.Ioc 0 ⌊16*U⌋₊, ‖α m‖ ≤ Cα)
    (hβ : ∀ s ∈ Finset.Ioc 0 ⌊2*V⌋₊, ‖β s‖ ≤ Cβ) :
    markedPhysicalEndpointNorm P M Z (fun j => bandReciprocalMass (P j)) α β ≤
      Real.sqrt (32*U*V)*(Cα*Cβ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCα hCβ), ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 32*U*V)]
  exact markedPhysicalEndpointEnergy_box P hP hdis M Z hν hU hV hZ α β hCα hCβ hα hβ

end ArtinMatthews
