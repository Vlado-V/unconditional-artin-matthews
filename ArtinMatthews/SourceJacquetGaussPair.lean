module

public import ArtinMatthews.SIntegerResidueGauss
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.NumberTheory.DirichletL.Detector.Gauss


set_option backward.privateInPublic true
@[expose] public section

/-! The actual standard-phase normalized Gauss constants in the
Jacquet table. Their cubic pair cancels exactly, and their unit norm
comes from the proved primitive local character. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open StandardAdelic VaryingKummerAnalytic
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)

def sourceJacquetGauss (j : ℕ) : ℂ :=
  residueSourceTau S₀ P hP a ha (χ ^ j) / (Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℂ)

theorem sourceJacquetGauss_norm (hbad : P ∉ traceBadPlaces F) (j : ℕ) (hj : χ ^ j ≠ 1) :
    ‖sourceJacquetGauss F P S₀ hP a ha χ j‖ = 1 := by
  have hq : 0 < (Ideal.absNorm P.asIdeal : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))
  rw [sourceJacquetGauss, norm_div, residueSourceTau_norm S₀ P hP a ha hbad _ hj,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hq).ne']

theorem sourceJacquetGauss_two_four (hbad : P ∉ traceBadPlaces F) (hχ : orderOf χ = 6) :
    sourceJacquetGauss F P S₀ hP a ha χ 2 * sourceJacquetGauss F P S₀ hP a ha χ 4 = 1 := by
  let R := (𝓞 F) ⧸ P.asIdeal
  let : Field R := Ideal.Quotient.field _
  let : Finite R := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype R := Fintype.ofFinite _
  have hc : Fintype.card R = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hn : χ ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_iff_pow_eq_one.mpr he
    rw [hχ] at hd
    norm_num at hd
  have hsix : χ ^ 6 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hχ])
  have hinv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    exact hsix
  have hminus : (χ ^ 2) (-1 : R) = 1 := by
    rw [MulChar.pow_apply' _ (by decide : 2 ≠ 0), ← map_pow]
    simp
  have hp : residueSourceTau S₀ P hP a ha (χ ^ 2) * residueSourceTau S₀ P hP a ha (χ ^ 4) =
      (Ideal.absNorm P.asIdeal : ℂ) := by
    have hh := ProbeGauss.gauss_inverse_pair (χ ^ 2) (residueSourcePhase S₀ P hP a ha) hn
      (residueSourcePhase_primitive S₀ P hP a ha hbad)
    rw [hminus, one_mul, hc] at hh
    simpa only [residueSourceTau, tsum_fintype, gaussSum, hinv] using hh
  have hq : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  unfold sourceJacquetGauss
  rw [div_mul_div_comm, hp, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _),
    Complex.ofReal_natCast, div_self hq]

end
end ArtinMatthews
