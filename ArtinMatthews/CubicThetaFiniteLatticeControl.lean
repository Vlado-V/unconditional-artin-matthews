module

public import ArtinMatthews.CubicThetaFiniteSymplectic
public import ArtinMatthews.CubicThetaFiniteCosetAction
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete lattice conditions for the Eisenstein finite symplectic action. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators MatrixGroups Classical
open Matrix
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport

variable {ι : Type*}

/-- An integer scalar preserves every rational finite-adelic lattice. -/
theorem finiteScale_int_lattice (z : ℤ) (r : ℚ) (hr : r ≠ 0)
    {x : ι → AQf} (hx : x ∈ finiteLattice r hr) :
    finiteScale (z : ℚ) x ∈ finiteLattice r hr := by
  rw [finiteLattice_mem_iff] at hx ⊢
  have he : finiteScale r⁻¹ (finiteScale (z : ℚ) x) =
      finiteScale (z : ℚ) (finiteScale r⁻¹ x) := by
    rw [finiteScale_mul, finiteScale_mul, mul_comm]
  rw [he]
  intro i
  change algebraMap ℚ AQf (z : ℚ) * _ ∈ integralAdele
  rw [map_intCast]
  exact integralAdele.mul_mem (intCast_mem_integralAdele z) (hx i)

/-- Exact divisibility of rational scales suffices for lattice transport. -/
theorem finiteScale_lattice_of_mul_eq (r s t : ℚ) (hr : r ≠ 0) (ht : t ≠ 0)
    (z : ℤ) (hscale : s * r = t * z)
    {x : ι → AQf} (hx : x ∈ finiteLattice r hr) :
    finiteScale s x ∈ finiteLattice t ht := by
  rw [finiteLattice_mem_iff] at hx ⊢
  rw [finiteScale_mul]
  have he : t⁻¹ * s = (z : ℚ) * r⁻¹ := by
    apply (mul_right_cancel₀ hr)
    field_simp
    exact hscale
  rw [he, ← finiteScale_mul]
  intro i
  change algebraMap ℚ AQf (z : ℚ) * _ ∈ integralAdele
  rw [map_intCast]
  exact integralAdele.mul_mem (intCast_mem_integralAdele z) (hx i)

variable [Fintype ι] [DecidableEq ι]

theorem finiteIntegerMatrixAction_diagonal (z : ℤ) (x : ι → AQf) :
    finiteIntegerMatrixAction (Matrix.diagonal (fun _ : ι => z)) x =
      finiteScale (z : ℚ) x := by
  funext i
  simp [finiteIntegerMatrixAction, Matrix.diagonal, finiteScale]

omit [DecidableEq ι] in
theorem finiteIntegerMatrixAction_zero (A : Matrix ι ι ℤ) :
    finiteIntegerMatrixAction A 0 = 0 := by
  funext i
  simp [finiteIntegerMatrixAction]

omit [Fintype ι] [DecidableEq ι] in
theorem finiteScale_zero (r : ℚ) : finiteScale r (0 : ι → AQf) = 0 := by
  funext i
  simp [finiteScale]

/-- Forward lattice control; the lower-left divisibility includes precisely
both half-translation conditions in the Heisenberg model. -/
theorem eisensteinFiniteSymplectic_lattice_control_forward
    (M : ℤ) (hM : M ≠ 0) (heven : 2 ∣ M) (γ : SL(2, ℤ))
    (hc : 6 * M ^ 2 ∣ γ 1 0) :
    (∀ p ∈ finiteLattice (M : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hM)),
      finiteMomentum (eisensteinFiniteSymplectic γ) p 0 ∈
        finiteLattice (M : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hM)) ∧
      finitePosition (eisensteinFiniteSymplectic γ) p 0 ∈
        finiteLattice (M : ℚ) (by exact_mod_cast hM) ∧
      finiteScale (1 / 2) (finitePosition (eisensteinFiniteSymplectic γ) p 0) ∈
        finiteLattice (M : ℚ) (by exact_mod_cast hM)) ∧
    (∀ q ∈ finiteLattice (M : ℚ) (by exact_mod_cast hM),
      finiteMomentum (eisensteinFiniteSymplectic γ) 0 q ∈
        finiteLattice (M : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hM)) ∧
      finitePosition (eisensteinFiniteSymplectic γ) 0 q ∈
        finiteLattice (M : ℚ) (by exact_mod_cast hM) ∧
      finiteScale (1 / 2) (finiteMomentum (eisensteinFiniteSymplectic γ) 0 q) ∈
        finiteLattice (M : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hM))) := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  obtain ⟨k, hk⟩ := hc
  obtain ⟨l, hl⟩ := heven
  constructor
  · intro p hp
    simp only [eisensteinFiniteSymplectic_momentum, eisensteinFiniteSymplectic_position,
      finiteIntegerMatrixAction_zero, add_zero, finiteIntegerMatrixAction_diagonal]
    have hAdj := finiteIntegerMatrixAction_lattice eisensteinGramAdjInt _ _ hp
    refine ⟨finiteScale_int_lattice _ _ _ hp, ?_, ?_⟩
    · apply finiteScale_lattice_of_mul_eq _ _ _ (inv_ne_zero hMq) hMq (2 * k) ?_ hAdj
      have hkq : (γ 1 0 : ℚ) = 6 * (M : ℚ) ^ 2 * k := by exact_mod_cast hk
      rw [hkq]
      push_cast
      field_simp
      ring
    · rw [finiteScale_mul]
      apply finiteScale_lattice_of_mul_eq _ _ _ (inv_ne_zero hMq) hMq k ?_ hAdj
      have hkq : (γ 1 0 : ℚ) = 6 * (M : ℚ) ^ 2 * k := by exact_mod_cast hk
      rw [hkq]
      field_simp
      ring
  · intro q hq
    simp only [eisensteinFiniteSymplectic_momentum, eisensteinFiniteSymplectic_position,
      finiteIntegerMatrixAction_zero, finiteScale_zero, zero_add, finiteIntegerMatrixAction_diagonal]
    have hG := finiteIntegerMatrixAction_lattice (γ 0 1 • eisensteinGramInt) _ _ hq
    refine ⟨?_, finiteScale_int_lattice _ _ _ hq, ?_⟩
    · have hh := finiteScale_lattice_of_mul_eq (M : ℚ) 1 (M : ℚ)⁻¹ hMq
        (inv_ne_zero hMq) (M ^ 2) ?_ hG
      · simpa only [finiteScale_one] using hh
      · push_cast
        field_simp
    · apply finiteScale_lattice_of_mul_eq (M : ℚ) (1 / 2) (M : ℚ)⁻¹ hMq
        (inv_ne_zero hMq) (2 * l ^ 2) ?_ hG
      have hlq : (M : ℚ) = 2 * l := by exact_mod_cast hl
      rw [hlq]
      push_cast
      field_simp

/-- The exact inverse-lattice hypothesis required by the finite Weil coset
transport theorem, derived from an ordinary integral congruence. -/
theorem eisensteinFiniteSymplectic_baseLatticeControl
    (M : ℤ) (hM : M ≠ 0) (heven : 2 ∣ M) (γ : SL(2, ℤ))
    (hc : 6 * M ^ 2 ∣ γ 1 0) :
    finiteBaseLatticeControl (M : ℚ) (by exact_mod_cast hM)
      (eisensteinFiniteSymplectic γ) := by
  have hci : 6 * M ^ 2 ∣ γ⁻¹ 1 0 := by
    have hi : γ⁻¹ 1 0 = -γ 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv]
      simp [Matrix.adjugate_fin_two]
    rw [hi]
    exact dvd_neg.mpr hc
  unfold finiteBaseLatticeControl
  rw [← map_inv]
  exact eisensteinFiniteSymplectic_lattice_control_forward M hM heven γ⁻¹ hci

end ArtinMatthews
