module

public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.KummerSplittingDegreeNonpowers
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! An actual integral tower power basis with controlled embeddings. -/

noncomputable section
namespace ArtinMatthews

/-- A power below the defining radical exponent has a bound independent of
the choice of its complex conjugate. -/
theorem radical_power_norm_le {z : ℂ} {a : ℤ} {q j : ℕ}
    (hz : z ^ q = (a : ℂ)) (hj : j ≤ q) :
    ‖z‖ ^ j ≤ max (1 : ℝ) |(a : ℝ)| := by
  have hpow : ‖z‖ ^ q = |(a : ℝ)| := by
    simpa only [norm_pow, Complex.norm_intCast] using congrArg norm hz
  by_cases h : ‖z‖ ≤ 1
  · exact (pow_le_one₀ (norm_nonneg z) h).trans (le_max_left _ _)
  · exact ((pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hj).trans_eq hpow).trans
      (le_max_right _ _)

theorem primeCyclotomicPowerBasis_dim {q : ℕ} (hq : q.Prime) :
    (primeCyclotomicPowerBasis q).dim = q - 1 :=
  (primeCyclotomicPowerBasis q).finrank.symm.trans (finrank_primeCyclotomicField hq)

theorem primeKummerRelativePowerBasis_dim {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    (primeKummerRelativePowerBasis q a).dim = q := by
  apply (primeKummerRelativePowerBasis q a).finrank.symm.trans
  exact prime_radical_adjoin_finrank (primeCyclotomicField q) hq
    (finrank_primeCyclotomicField hq) (by exact_mod_cast ha0)
    (rat_pow_ne_int_of_natAbs_le ha0 ha1 ham1 haq)
    (by simpa only [Rat.cast_intCast] using primeRadicalRoot_pow hq.pos a)

/-- The actual relative-adjoin model has an integral rational basis of exactly
the established degree, and every embedding of every basis vector has norm at most `q`. -/
theorem primeKummerTower_integral_bounded_basis {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    ∃ b : Module.Basis (Fin (q * (q - 1))) ℚ (primeKummerTowerField q a),
      (∀ i, IsIntegral ℤ (b i)) ∧
      ∀ (σ : primeKummerTowerField q a →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ (q : ℝ) := by
  classical
  let E := primeCyclotomicField q
  let L := primeKummerTowerField q a
  let pe : PowerBasis ℚ E := primeCyclotomicPowerBasis q
  let pr : PowerBasis E L := primeKummerRelativePowerBasis q a
  let z : L := algebraMap E L pe.gen
  let r : L := pr.gen
  have hzpow : z ^ q = 1 := by
    apply Subtype.ext
    change primeCyclotomicRoot q ^ q = (1 : ℂ)
    exact primeCyclotomicRoot_pow hq.pos
  have hrpow : r ^ q = (a : L) := by
    apply Subtype.ext
    change primeRadicalRoot q a ^ q = (a : ℂ)
    exact primeRadicalRoot_pow hq.pos a
  have hzi : IsIntegral ℤ z := by
    apply IsIntegral.of_pow hq.pos
    rw [hzpow]
    exact isIntegral_one
  have hri : IsIntegral ℤ r := by
    apply IsIntegral.of_pow hq.pos
    rw [hrpow]
    exact isIntegral_algebraMap
  let b : Module.Basis (Fin pe.dim × Fin pr.dim) ℚ L := pe.basis.smulTower pr.basis
  have hb (ij : Fin pe.dim × Fin pr.dim) :
      b ij = z ^ (ij.1 : ℕ) * r ^ (ij.2 : ℕ) := by
    change (pe.basis.smulTower pr.basis) ij =
      (algebraMap E L pe.gen) ^ (ij.1 : ℕ) * pr.gen ^ (ij.2 : ℕ)
    rw [Module.Basis.smulTower_apply, pe.basis_eq_pow, pr.basis_eq_pow,
      Algebra.smul_def, map_pow]
  have hpe : pe.dim = q - 1 := primeCyclotomicPowerBasis_dim hq
  have hpr : pr.dim = q := primeKummerRelativePowerBasis_dim ha0 ha1 ham1 hq haq
  have hcard : Fintype.card (Fin pe.dim × Fin pr.dim) = q * (q - 1) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hpe, hpr]
    exact Nat.mul_comm _ _
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨b.reindex e, ?_, ?_⟩
  · intro i
    rw [Module.Basis.reindex_apply, hb]
    exact (hzi.pow _).mul (hri.pow _)
  · intro σ i
    have hσz : (σ z) ^ q = 1 := by rw [← map_pow, hzpow, map_one]
    have hσzn : ‖σ z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hσz hq.ne_zero
    have hσr : (σ r) ^ q = (a : ℂ) := by rw [← map_pow, hrpow, map_intCast]
    have hj : ((e.symm i).2 : ℕ) ≤ q := by
      exact (e.symm i).2.isLt.le.trans_eq hpr
    have hB : max (1 : ℝ) |(a : ℝ)| ≤ q := by
      apply max_le
      · exact_mod_cast hq.one_lt.le
      · simpa only [Nat.cast_natAbs, Int.cast_abs] using
          (show (a.natAbs : ℝ) ≤ (q : ℝ) by exact_mod_cast haq)
    rw [Module.Basis.reindex_apply, hb, map_mul, map_pow, map_pow, norm_mul,
      norm_pow, norm_pow, hσzn, one_pow, one_mul]
    exact (radical_power_norm_le hσr hj).trans hB

/-- The bounded integral basis belongs to the original frozen concrete field
`primeKummerField`, via the actual identity of its scalar-restricted carrier. -/
theorem primeKummerField_integral_bounded_basis {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    ∃ b : Module.Basis (Fin (q * (q - 1))) ℚ (primeKummerField q a),
      (∀ i, IsIntegral ℤ (b i)) ∧
      ∀ (σ : primeKummerField q a →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ (q : ℝ) := by
  obtain ⟨b, hb, hheight⟩ := primeKummerTower_integral_bounded_basis ha0 ha1 ham1 hq haq
  let e : primeKummerTowerField q a ≃ₐ[ℚ] primeKummerField q a :=
    AlgEquiv.ofRingEquiv (f := primeKummerTowerRingEquiv q a) (fun _ => by simp)
  refine ⟨b.map e.toLinearEquiv, ?_, ?_⟩
  · intro i
    rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply]
    exact (hb i).map ((e.restrictScalars ℤ).toAlgHom)
  · intro σ i
    rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply]
    exact hheight (σ.comp e.toAlgHom) i

end ArtinMatthews
