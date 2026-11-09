module

public import ArtinMatthews.CubicSieveCorrection
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! The actual signed overflow polynomial evaluated at local densities. -/

noncomputable section
namespace ArtinMatthews

open Finset OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

def cubicSieveCorrectionModel (z : ℝ) (m : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ T ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m T * ∏ p ∈ T, g p

theorem cubicSieve_correctionModel_eq_blocks (z : ℝ) (m : ℕ) (g : ℕ → ℝ) :
    cubicSieveCorrectionModel z m g =
      ∑ j ∈ cubicSieveBlockIndices z,
        BonferroniDensity.elementarySum (cubicSieveBlock z j) g (2 * cubicSieveOrder m j + 1) *
          ∏ i ∈ (cubicSieveBlockIndices z).erase j,
            BonferroniDensity.densityPolynomial (2 * cubicSieveOrder m i) (cubicSieveBlock z i) g := by
  let B := cubicSieveBlockIndices z
  let L := cubicSieveBlock z
  let h := cubicSieveOrder m
  have hdis : (B : Set ℕ).Pairwise fun i j => Disjoint (L i) (L j) :=
    fun i _ j _ hij => cubicSieveBlock_disjoint z hij
  unfold cubicSieveCorrectionModel cubicSieveCorrectionCoeff
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hh := DisjointBlockExpansion.correctionCoefficient_density B L hdis h g j hj
  rw [show B.biUnion L = Nat.primesLE ⌊z⌋₊ from cubicSieveBlock_union z] at hh
  exact hh

def cubicSievePrimeDivisorModel (s : ℝ) (p : ℕ) : ℝ :=
  2 * Real.exp (-(s * Real.log (p : ℝ))) - Real.exp (-(s * Real.log (p : ℝ))) ^ 2

def cubicSievePrimeDivisorDensity (p : ℕ) : ℝ :=
  2 * (p : ℝ)⁻¹ - ((p : ℝ)⁻¹) ^ 2

def cubicSievePrimeDivisorDensityDerivative (p : ℕ) : ℝ :=
  -2 * Real.log (p : ℝ) * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)

theorem cubicSieve_primeDivisorModel_eq_rpow {p : ℕ} (hp : 0 < p) (s : ℝ) :
    cubicSievePrimeDivisorModel s p = 2 * (p : ℝ) ^ (-s) - (p : ℝ) ^ (-2 * s) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp
  rw [cubicSievePrimeDivisorModel, Real.rpow_def_of_pos hp₀, Real.rpow_def_of_pos hp₀, sq,
    ← Real.exp_add]
  congr 1
  · congr 1
    congr 1
    ring
  · congr 1
    ring

theorem cubicSieve_primeDivisorModel_one {p : ℕ} (hp : 0 < p) :
    cubicSievePrimeDivisorModel 1 p = cubicSievePrimeDivisorDensity p := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [cubicSievePrimeDivisorModel, cubicSievePrimeDivisorDensity, one_mul, Real.exp_neg,
    Real.exp_log hp₀]

theorem cubicSieve_primeDivisorModel_hasDerivAt_one {p : ℕ} (hp : 0 < p) :
    HasDerivAt (fun s => cubicSievePrimeDivisorModel s p)
      (cubicSievePrimeDivisorDensityDerivative p) 1 := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp
  have h := (((hasDerivAt_id (1 : ℝ)).mul_const (Real.log (p : ℝ))).neg.exp)
  convert (h.const_mul 2).sub (h.pow 2) using 1
  · funext s
    simp only [cubicSievePrimeDivisorModel, Pi.sub_apply, Pi.pow_apply, id_eq, Pi.neg_apply]
  · simp only [cubicSievePrimeDivisorDensityDerivative, id_eq, Pi.neg_apply, one_mul,
      Real.exp_neg, Real.exp_log hp₀, Nat.cast_ofNat]
    ring

theorem cubicSieve_primeDivisorDensity_complement (p : ℕ) :
    1 - cubicSievePrimeDivisorDensity p = (1 - (p : ℝ)⁻¹) ^ 2 := by
  unfold cubicSievePrimeDivisorDensity
  ring

theorem cubicSieve_primeDivisorDensity_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ cubicSievePrimeDivisorDensity p ∧ cubicSievePrimeDivisorDensity p ≤ 3 / 4 ∧
      cubicSievePrimeDivisorDensity p ≤ 2 * (p : ℝ)⁻¹ := by
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp₀ : (0 : ℝ) < p := by linarith only [hp₂]
  have hi : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp₂
  have hi₀ := inv_nonneg.mpr hp₀.le
  refine ⟨?_, ?_, ?_⟩
  · unfold cubicSievePrimeDivisorDensity
    nlinarith only [mul_nonneg hi₀ (show 0 ≤ 2 - (p : ℝ)⁻¹ by linarith only [hi])]
  · have hsq := mul_le_mul (show (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ by linarith only [hi])
      (show (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ by linarith only [hi])
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith only [hi] : 0 ≤ 1 - (p : ℝ)⁻¹)
    nlinarith only [hsq, cubicSieve_primeDivisorDensity_complement p]
  · exact sub_le_self _ (sq_nonneg _)

theorem cubicSieve_primeDivisorDensityDerivative_abs_le {p : ℕ} (hp : p.Prime) :
    |cubicSievePrimeDivisorDensityDerivative p| ≤ Real.log (p : ℝ) * cubicSievePrimeDivisorDensity p := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hi₀ : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hp₁)
  have hi₁ : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp₁
  have hlog := Real.log_nonneg hp₁
  have hnonpos : cubicSievePrimeDivisorDensityDerivative p ≤ 0 := by
    unfold cubicSievePrimeDivisorDensityDerivative
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hlog) hi₀)
      (sub_nonneg.mpr hi₁)
  rw [abs_of_nonpos hnonpos]
  calc
    _ = (Real.log (p : ℝ) * (p : ℝ)⁻¹) * (2 * (1 - (p : ℝ)⁻¹)) := by
      unfold cubicSievePrimeDivisorDensityDerivative
      ring
    _ ≤ (Real.log (p : ℝ) * (p : ℝ)⁻¹) * (2 - (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (by linarith only [hi₀]) (mul_nonneg hlog hi₀)
    _ = _ := by unfold cubicSievePrimeDivisorDensity; ring

end ArtinMatthews
