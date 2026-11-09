module

public import OAI.RepresentationTheory.Theta.CosetTests


set_option backward.privateInPublic true
@[expose] public section

/-! Finite periodic weights as actual compact locally constant adelic test functions. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.CosetTests.PoissonAutomorphyConstruction
open OAI.RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N]

/-- A finite residue weight extended by zero off integral finite adeles. -/
def finiteResidueTest (w : (ι → ZMod N) → ℂ) : finiteSchwartz ι :=
  ∑ r : ι → ZMod N, w r •
    latticeCosetTest (N : ℚ) (by exact_mod_cast (NeZero.ne N)) (residuePoint r)

omit [Fintype ι] [DecidableEq ι] in
theorem integerFinite_sub_residue_mem_iff (m : ι → ℤ) (r : ι → ZMod N) :
    integerFinite m - residuePoint r ∈
      finiteLattice (N : ℚ) (by exact_mod_cast (NeZero.ne N)) ↔
        (fun i => (m i : ZMod N)) = r := by
  have he : integerFinite m - residuePoint r =
      integerFinite (fun i => m i - ((r i).val : ℤ)) := by
    ext i
    simp [integerFinite, residuePoint]
  rw [he, integerFinite_mem_finiteLattice_iff N (NeZero.pos N)]
  constructor
  · intro h
    ext i
    have hi := (ZMod.intCast_eq_intCast_iff_dvd_sub ((r i).val : ℤ) (m i) N).mpr (h i)
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hi.symm
  · intro h i
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub ((r i).val : ℤ) (m i) N).mp
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using (congrFun h i).symm

/-- The adelic test takes exactly the prescribed residue weight at integers. -/
theorem finiteResidueTest_integer (w : (ι → ZMod N) → ℂ) (m : ι → ℤ) :
    (finiteResidueTest w).val (integerFinite m) = w (fun i => (m i : ZMod N)) := by
  have ht (r : ι → ZMod N) :
      latticeCosetIndicator (N : ℚ) (by exact_mod_cast (NeZero.ne N))
        (residuePoint r) (integerFinite m) =
          if (fun i => (m i : ZMod N)) = r then 1 else 0 := by
    unfold latticeCosetIndicator
    by_cases h : (fun i => (m i : ZMod N)) = r
    · rw [ite_eq_left h, latticeIndicator_of_mem _ _
        ((integerFinite_sub_residue_mem_iff m r).mpr h)]
    · rw [ite_eq_right h, latticeIndicator_of_notMem _ _
        (fun hm => h ((integerFinite_sub_residue_mem_iff m r).mp hm))]
  simp only [finiteResidueTest, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, latticeCosetTest_apply, ht]
  simp

/-- Rational points in the support are honest integral vectors. -/
theorem finiteResidueTest_rational_support (w : (ι → ZMod N) → ℂ)
    (x : ι → ℚ) (hx : (finiteResidueTest w).val (finiteDiagonal x) ≠ 0) :
    ∃ m : ι → ℤ, ∀ i, (m i : ℚ) = x i := by
  have hsum : ∑ r : ι → ZMod N,
      w r * latticeCosetIndicator (N : ℚ)
        (by exact_mod_cast (NeZero.ne N)) (residuePoint r) (finiteDiagonal x) ≠ 0 := by
    simpa only [finiteResidueTest, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, latticeCosetTest_apply] using hx
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hmem : finiteDiagonal x - residuePoint r ∈
      finiteLattice (N : ℚ) (by exact_mod_cast (NeZero.ne N)) := by
    by_contra h
    exact hr (by rw [latticeCosetIndicator, latticeIndicator_of_notMem _ _ h, mul_zero])
  have hi : finiteDiagonal x ∈ integralVectors := by
    have hd := finiteLattice_nat_subset_integral N (NeZero.pos N) hmem
    have hrI : residuePoint r ∈ integralVectors := by
      intro i
      exact intCast_mem_integralAdele ((r i).val : ℤ)
    simpa only [sub_add_cancel] using integralVectors.add_mem hd hrI
  have hxi : ∀ i, ∃ m : ℤ, (m : ℚ) = x i := fun i =>
    (rational_integral_iff (x i)).mp (hi i)
  choose m hm using hxi
  exact ⟨m, hm⟩

end ArtinMatthews
