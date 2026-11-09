module

public import ArtinMatthews.CubicThetaFiniteLatticeControl


set_option backward.privateInPublic true
@[expose] public section

/-! Integer residue centers have integral Heisenberg phase and transform by d. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators MatrixGroups Classical
open Matrix
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction
open OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport

variable {ι : Type*} [Fintype ι]

theorem finiteIntegerMatrixAction_integer (A : Matrix ι ι ℤ) (m : ι → ℤ) :
    finiteIntegerMatrixAction A (integerFinite m) =
      integerFinite (fun i => ∑ j, A i j * m j) := by
  funext i
  simp [finiteIntegerMatrixAction, integerFinite]

omit [Fintype ι] in
theorem integerFinite_mem_inverse_integer_lattice (M : ℤ) (hM : M ≠ 0) (m : ι → ℤ) :
    integerFinite m ∈ finiteLattice (M : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hM)) := by
  rw [finiteLattice_mem_iff]
  intro i
  simp only [inv_inv, finiteScale, integerFinite, map_intCast]
  exact integralAdele.mul_mem (intCast_mem_integralAdele M) (intCast_mem_integralAdele (m i))

/-- A finite integral center is sent to d times that center in position. -/
theorem eisensteinFiniteSymplectic_integer_position (γ : SL(2, ℤ)) (m : Fin 2 → ℤ) :
    finitePosition (eisensteinFiniteSymplectic γ) 0 (integerFinite m) =
      integerFinite (fun i => γ 1 1 * m i) := by
  rw [eisensteinFiniteSymplectic_position, finiteIntegerMatrixAction_zero,
    finiteScale_zero, zero_add, finiteIntegerMatrixAction_integer]
  funext i
  fin_cases i <;> simp [integerFinite, Matrix.diagonal]

/-- The half-phase is integral because the Eisenstein Gram form is even. -/
theorem eisensteinFiniteSymplectic_integer_phase (γ : SL(2, ℤ)) (m : Fin 2 → ℤ) :
    (∑ i, finiteMomentum (eisensteinFiniteSymplectic γ) 0 (integerFinite m) i *
      finiteScale (1 / 2)
        (finitePosition (eisensteinFiniteSymplectic γ) 0 (integerFinite m)) i) ∈ integralAdele := by
  have hhalf : 2 * algebraMap ℚ AQf (1 / 2) = 1 := by
    calc
      2 * algebraMap ℚ AQf (1 / 2) = algebraMap ℚ AQf (2 * (1 / 2)) := by
        rw [map_mul, map_ofNat]
      _ = 1 := by norm_num
  have he : (∑ i, finiteMomentum (eisensteinFiniteSymplectic γ) 0 (integerFinite m) i *
      finiteScale (1 / 2)
        (finitePosition (eisensteinFiniteSymplectic γ) 0 (integerFinite m)) i) =
      ((γ 0 1 * γ 1 1 * (m 0 ^ 2 - m 0 * m 1 + m 1 ^ 2) : ℤ) : AQf) := by
    rw [eisensteinFiniteSymplectic_momentum, eisensteinFiniteSymplectic_integer_position,
      finiteIntegerMatrixAction_zero, zero_add]
    calc
      _ = (2 * algebraMap ℚ AQf (1 / 2)) *
          ((γ 0 1 * γ 1 1 * (m 0 ^ 2 - m 0 * m 1 + m 1 ^ 2) : ℤ) : AQf) := by
        simp [finiteIntegerMatrixAction, integerFinite, finiteScale,
          eisensteinGramInt, Fin.sum_univ_two]
        ring
      _ = _ := by rw [hhalf, one_mul]
  rw [he]
  exact intCast_mem_integralAdele _

/-- All three concrete coset-transport hypotheses for integer centers. -/
theorem eisensteinFiniteSymplectic_integer_coset_conditions
    (M : ℤ) (hM : M ≠ 0) (γ : SL(2, ℤ)) (m : Fin 2 → ℤ) :
    finiteMomentum (eisensteinFiniteSymplectic γ) 0 (integerFinite m) ∈
        finiteLattice (M : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast hM)) ∧
    finitePosition (eisensteinFiniteSymplectic γ) 0 (integerFinite m) -
        integerFinite (fun i => γ 1 1 * m i) ∈
        finiteLattice (M : ℚ) (by exact_mod_cast hM) ∧
    (∑ i, finiteMomentum (eisensteinFiniteSymplectic γ) 0 (integerFinite m) i *
      finiteScale (1 / 2)
        (finitePosition (eisensteinFiniteSymplectic γ) 0 (integerFinite m)) i) ∈ integralAdele := by
  refine ⟨?_, ?_, eisensteinFiniteSymplectic_integer_phase γ m⟩
  · rw [eisensteinFiniteSymplectic_momentum, finiteIntegerMatrixAction_zero,
      zero_add, finiteIntegerMatrixAction_integer]
    exact integerFinite_mem_inverse_integer_lattice M hM _
  · rw [eisensteinFiniteSymplectic_integer_position, sub_self]
    exact (finiteLattice (M : ℚ) (by exact_mod_cast hM)).zero_mem

/-- Natural moduli version, matching `finiteResidueTest`. -/
theorem eisensteinFiniteSymplectic_baseLatticeControl_nat
    (M : ℕ) [NeZero M] (heven : 2 ∣ M) (γ : SL(2, ℤ))
    (hc : 6 * (M : ℤ) ^ 2 ∣ γ 1 0) :
    finiteBaseLatticeControl (M : ℚ) (by exact_mod_cast (NeZero.ne M))
      (eisensteinFiniteSymplectic γ) := by
  simpa only [Int.cast_natCast] using
    eisensteinFiniteSymplectic_baseLatticeControl (M : ℤ)
      (by exact_mod_cast (NeZero.ne M)) (by exact_mod_cast heven) γ hc

/-- Exact residue-center transport for the actual finite periodic test. -/
theorem eisensteinFiniteSymplectic_residue_coset_conditions
    (M : ℕ) [NeZero M] (γ : SL(2, ℤ)) (r : Fin 2 → ZMod M) :
    finiteMomentum (eisensteinFiniteSymplectic γ) 0 (residuePoint r) ∈
        finiteLattice (M : ℚ)⁻¹ (inv_ne_zero (by exact_mod_cast (NeZero.ne M))) ∧
    finitePosition (eisensteinFiniteSymplectic γ) 0 (residuePoint r) -
        residuePoint (fun i => (γ 1 1 : ZMod M) * r i) ∈
        finiteLattice (M : ℚ) (by exact_mod_cast (NeZero.ne M)) ∧
    (∑ i, finiteMomentum (eisensteinFiniteSymplectic γ) 0 (residuePoint r) i *
      finiteScale (1 / 2)
        (finitePosition (eisensteinFiniteSymplectic γ) 0 (residuePoint r)) i) ∈ integralAdele := by
  let m : Fin 2 → ℤ := fun i => (r i).val
  have ha : residuePoint r = integerFinite m := rfl
  obtain ⟨hp, _, hphase⟩ := eisensteinFiniteSymplectic_integer_coset_conditions
    (M : ℤ) (by exact_mod_cast (NeZero.ne M)) γ m
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ha, Int.cast_natCast] using hp
  · rw [ha, eisensteinFiniteSymplectic_integer_position]
    apply (integerFinite_sub_residue_mem_iff _ _).mpr
    funext i
    simp [m]
  · simpa only [ha] using hphase

end ArtinMatthews
