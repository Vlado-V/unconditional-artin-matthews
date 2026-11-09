module

public import ArtinMatthews.MarkedMinorArcBlockOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite weighted-to-counting L2 conjugation and endpoint square-root bounds. -/
noncomputable section
namespace ArtinMatthews

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

def markedWeightedCountingVector {ι : Type*} (mass : ι → ℝ) (f : ι → ℂ) (i : ι) : ℂ :=
  (Real.sqrt (mass i):ℂ)*f i

def markedWeightedCountingMatrix {ι : Type*} (mass : ι → ℝ) (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (Real.sqrt (mass i):ℂ)*K i j*(Real.sqrt (mass j):ℂ)

def markedWeightedMatrixApply {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (K : Matrix ι ι ℂ) (f : ι → ℂ) (i : ι) : ℂ :=
  ∑ j, K i j*(mass j:ℂ)*f j

theorem markedWeightedCountingVector_energy {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (hm : ∀ i, 0 ≤ mass i) (f : ι → ℂ) :
    (∑ i, ‖markedWeightedCountingVector mass f i‖^2) = ∑ i, mass i*‖f i‖^2 := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [markedWeightedCountingVector, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hm i)]

/-- The genuine weighted matrix action is conjugated to the literal matrix
with square-root mass at both endpoints. -/
theorem markedWeightedCountingMatrix_mulVec {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (hm : ∀ i, 0 ≤ mass i) (K : Matrix ι ι ℂ) (f : ι → ℂ) :
    markedWeightedCountingMatrix mass K *ᵥ markedWeightedCountingVector mass f =
      markedWeightedCountingVector mass (markedWeightedMatrixApply mass K f) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, markedWeightedCountingMatrix,
    markedWeightedCountingVector, markedWeightedMatrixApply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (Real.sqrt (mass j):ℂ)*(Real.sqrt (mass j):ℂ) = (mass j:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hm j)
  calc
    _ = (Real.sqrt (mass i):ℂ)*K i j*
        ((Real.sqrt (mass j):ℂ)*(Real.sqrt (mass j):ℂ))*f j := by ring
    _ = _ := by rw [hs]; ring

/-- Operator estimates in counting L2 transport to the actual finite weighted
energy without any multiplicity or cardinality loss. -/
theorem markedWeightedMatrix_energy_le_of_counting_norm {ι : Type*}
    [Fintype ι] [DecidableEq ι] (mass : ι → ℝ) (hm : ∀ i, 0 ≤ mass i)
    (K : Matrix ι ι ℂ) {C : ℝ} (hC : 0 ≤ C) (hK : ‖markedWeightedCountingMatrix mass K‖ ≤ C)
    (f : ι → ℂ) :
    (∑ i, mass i*‖markedWeightedMatrixApply mass K f i‖^2) ≤
      C^2*(∑ i, mass i*‖f i‖^2) := by
  have hh := markedMinorMatrix_energy_le_of_norm (markedWeightedCountingMatrix mass K)
    hC hK (markedWeightedCountingVector mass f)
  rw [markedWeightedCountingMatrix_mulVec mass hm K f,
    markedWeightedCountingVector_energy mass hm, markedWeightedCountingVector_energy mass hm] at hh
  exact hh

theorem markedProductMass_sqrt_endpoint_le {m C Y : ℝ} (hY : 0 < Y)
    (hm : m ≤ C/Y) : Real.sqrt (Y*m) ≤ Real.sqrt C := by
  apply Real.sqrt_le_sqrt
  have hh := (le_div_iff₀ hY).mp hm
  nlinarith

theorem markedProductMass_sqrt_pair_le {m n C Y : ℝ} (hm0 : 0 ≤ m)
    (hC : 0 ≤ C) (hY : 0 < Y) (hm : m ≤ C/Y) (hn : n ≤ C/Y) :
    Real.sqrt (m*n) ≤ C/Y := by
  rw [Real.sqrt_mul hm0]
  have hh := mul_le_mul (Real.sqrt_le_sqrt hm) (Real.sqrt_le_sqrt hn)
    (Real.sqrt_nonneg n) (Real.sqrt_nonneg (C/Y))
  simpa only [Real.mul_self_sqrt (div_nonneg hC hY.le)] using hh

end ArtinMatthews
