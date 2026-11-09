module

public import ArtinMatthews.CubicThetaFiniteCosetAction


set_option backward.privateInPublic true
@[expose] public section

/-! Exact integral linear algebra on finite-adelic rational lattices. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction

variable {ι : Type*} [Fintype ι]

/-- An integral matrix acting on actual finite adele coordinates. -/
def finiteIntegerMatrixAction (M : Matrix ι ι ℤ) (x : ι → AQf) : ι → AQf :=
  fun i => ∑ j, (M i j : AQf) * x j

theorem finiteIntegerMatrixAction_integral (M : Matrix ι ι ℤ)
    {x : ι → AQf} (hx : x ∈ integralVectors) :
    finiteIntegerMatrixAction M x ∈ integralVectors := by
  intro i
  apply integralAdele.sum_mem
  intro j _
  exact integralAdele.mul_mem (intCast_mem_integralAdele _) (hx j)

theorem finiteIntegerMatrixAction_scale (M : Matrix ι ι ℤ) (r : ℚ) (x : ι → AQf) :
    finiteIntegerMatrixAction M (finiteScale r x) =
      finiteScale r (finiteIntegerMatrixAction M x) := by
  funext i
  simp only [finiteIntegerMatrixAction, finiteScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every integral matrix preserves every rationally scaled integral lattice. -/
theorem finiteIntegerMatrixAction_lattice (M : Matrix ι ι ℤ)
    (r : ℚ) (hr : r ≠ 0) {x : ι → AQf} (hx : x ∈ finiteLattice r hr) :
    finiteIntegerMatrixAction M x ∈ finiteLattice r hr := by
  rw [finiteLattice_mem_iff] at hx ⊢
  rw [← finiteIntegerMatrixAction_scale]
  exact finiteIntegerMatrixAction_integral M hx

omit [Fintype ι] in
/-- Exact change of rational lattice scale. -/
theorem finiteScale_lattice_ratio (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    {x : ι → AQf} (hx : x ∈ finiteLattice r hr) :
    finiteScale (s / r) x ∈ finiteLattice s hs := by
  rw [finiteLattice_mem_iff] at hx ⊢
  rw [finiteScale_mul]
  have h : s⁻¹ * (s / r) = r⁻¹ := by field_simp
  rw [h]
  exact hx

end ArtinMatthews
