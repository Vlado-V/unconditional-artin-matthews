module

public import ArtinMatthews.KummerCyclotomicTowerBase
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.KummerCyclotomicTowerCyclic
public import ArtinMatthews.KummerSplittingDiscriminantHeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

/-! A bounded integral basis of the actual auxiliary field. The relative
radical degree may be any divisor of q; irreducibility is not assumed. -/
set_option maxHeartbeats 800000
noncomputable section
namespace ArtinMatthews

def twelfthKummerRelativePowerBasis (q : ℕ) (a : ℤ) :
    PowerBasis (twelfthCyclotomicField q) (twelfthKummerField q a) :=
  IntermediateField.adjoin.powerBasis ((primeRadicalRoot_isIntegral q a).tower_top)

theorem twelfthKummerRelativePowerBasis_dim_le (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    (twelfthKummerRelativePowerBasis q a).dim ≤ q := by
  rw [← (twelfthKummerRelativePowerBasis q a).finrank]
  exact Nat.le_of_dvd (NeZero.pos q) (twelfthKummerField_relative_finrank_dvd q a)

/-- Actual auxiliary-field integral rational basis, with height at most q. -/
theorem twelfthKummerField_integral_bounded_basis (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (haq : a.natAbs ≤ q) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ (twelfthKummerField q a))) ℚ
        (twelfthKummerField q a),
      (∀ i, IsIntegral ℤ (b i)) ∧
      ∀ (σ : twelfthKummerField q a →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ (q : ℝ) := by
  classical
  let F := twelfthCyclotomicField q
  let E := twelfthKummerField q a
  let pe : PowerBasis ℚ F := primeCyclotomicPowerBasis (12 * q)
  let pr : PowerBasis F E := twelfthKummerRelativePowerBasis q a
  let z : E := algebraMap F E pe.gen
  let r : E := pr.gen
  have hq : 0 < q := NeZero.pos q
  have h12q : 0 < 12 * q := Nat.mul_pos (by norm_num) hq
  have hzpow : z ^ (12 * q) = 1 := by
    apply Subtype.ext
    change primeCyclotomicRoot (12 * q) ^ (12 * q) = (1 : ℂ)
    exact primeCyclotomicRoot_pow h12q
  have hrpow : r ^ q = (a : E) := by
    apply Subtype.ext
    change primeRadicalRoot q a ^ q = (a : ℂ)
    exact primeRadicalRoot_pow hq a
  have hzi : IsIntegral ℤ z := by
    apply IsIntegral.of_pow h12q
    rw [hzpow]
    exact isIntegral_one
  have hri : IsIntegral ℤ r := by
    apply IsIntegral.of_pow hq
    rw [hrpow]
    exact isIntegral_algebraMap
  let b : Module.Basis (Fin pe.dim × Fin pr.dim) ℚ E := pe.basis.smulTower pr.basis
  have hb (ij : Fin pe.dim × Fin pr.dim) :
      b ij = z ^ (ij.1 : ℕ) * r ^ (ij.2 : ℕ) := by
    change (pe.basis.smulTower pr.basis) ij =
      (algebraMap F E pe.gen) ^ (ij.1 : ℕ) * pr.gen ^ (ij.2 : ℕ)
    rw [Module.Basis.smulTower_apply, pe.basis_eq_pow, pr.basis_eq_pow,
      Algebra.smul_def, map_pow]
  have hpr : pr.dim ≤ q := twelfthKummerRelativePowerBasis_dim_le q a
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, ?_, ?_⟩
  · intro i
    rw [Module.Basis.reindex_apply, hb]
    exact (hzi.pow _).mul (hri.pow _)
  · intro σ i
    have hσz : (σ z) ^ (12 * q) = 1 := by rw [← map_pow, hzpow, map_one]
    have hσzn : ‖σ z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hσz (Nat.ne_of_gt h12q)
    have hσr : (σ r) ^ q = (a : ℂ) := by rw [← map_pow, hrpow, map_intCast]
    have hj : ((e.symm i).2 : ℕ) ≤ q := (e.symm i).2.isLt.le.trans hpr
    have hB : max (1 : ℝ) |(a : ℝ)| ≤ q := by
      apply max_le
      · exact_mod_cast hq
      · simpa only [Nat.cast_natAbs, Int.cast_abs] using
          (show (a.natAbs : ℝ) ≤ (q : ℝ) by exact_mod_cast haq)
    rw [Module.Basis.reindex_apply, hb, map_mul, map_pow, map_pow, norm_mul,
      norm_pow, norm_pow, hσzn, one_pow, one_mul]
    exact (radical_power_norm_le hσr hj).trans hB

end ArtinMatthews
