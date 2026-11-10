module

public import ArtinMatthews.ProbeEulerLocalAlgebra
public import ArtinMatthews.ProbeIdealRawSeries
public import ArtinMatthews.ProbeIdealHasSumTransport
public import ArtinMatthews.ProbeLocalSurvivorSum
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original Bool x Nat x Nat x Nat local series has the source's good
rational factor, with its actual constructed local Gauss correction. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem probeIdealRawLocal_hasSum (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    HasSum (probeIdealRawTerm K P χ η θ a b V)
      (ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (P.asIdeal)) V (θ * b)
        (η * θ⁻¹ * a)
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
          (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V)) := by
  have hq : (Ideal.absNorm (P.asIdeal) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      P.ne_bot
  have hs := probeLocalSurvivor_hasSum (Ideal.absNorm (P.asIdeal) : ℂ)
    ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6)
    (θ * b) (η * θ⁻¹ * a) V hq hV hW hE
  have ht : HasSum (fun j : ProbeLocalSurvivor =>
      probeIdealRawTerm K P χ η θ a b V (probeLocalSurvivorIndex j))
      (ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (P.asIdeal)) V (θ * b)
        (η * θ⁻¹ * a)
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
          (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V)) := by
    rw [probeIdealRaw_survivor_eq K P χ hχ hminus hchar η θ a b V hθ]
    exact hs
  exact probeIdeal_hasSum_transport K P χ hχ hminus
    (probeIdealRawTerm K P χ η θ a b V) _
    (probeIdealRawTerm_zero_of_coefficient K P χ η θ a b V) ht

theorem probeIdealRawLocalSeries_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    probeIdealRawLocalSeries K P χ η θ a b V =
      ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (P.asIdeal)) V (θ * b)
        (η * θ⁻¹ * a)
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
          (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V) :=
  (probeIdealRawLocal_hasSum K P χ hχ hminus hchar η θ a b V hθ hV hW hE).tsum_eq

theorem probeIdealRawLocal_summable_norm (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    Summable (fun i : ProbeLocalRawIndex => ‖probeIdealRawTerm K P χ η θ a b V i‖) :=
  (probeIdealRawLocal_hasSum K P χ hχ hminus hchar η θ a b V hθ hV hW hE).summable.norm

theorem probeIdealRawLocalNested_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (η θ a b V : ℂ) (hθ : θ ^ 6 = 1) (hV : ‖V‖ < 1) (hW : ‖θ * b‖ < 1)
    (hE : ‖(probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    (∑' e : Bool, ∑' l : ℕ, ∑' k : ℕ, ∑' r : ℕ,
      probeIdealRawTerm K P χ η θ a b V (e, l, k, r)) =
      ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (P.asIdeal)) V (θ * b)
        (η * θ⁻¹ * a)
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
          (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V) := by
  have hs := probeIdealRawLocal_hasSum K P χ hχ hminus hchar η θ a b V hθ hV hW hE
  have he : (∑' i : ProbeLocalRawIndex, probeIdealRawTerm K P χ η θ a b V i) =
      ∑' e : Bool, ∑' l : ℕ, ∑' k : ℕ, ∑' r : ℕ,
        probeIdealRawTerm K P χ η θ a b V (e, l, k, r) := by
    rw [hs.summable.tsum_prod]
    apply tsum_congr
    intro e
    rw [(hs.summable.prod_factor e).tsum_prod]
    apply tsum_congr
    intro l
    exact ((hs.summable.prod_factor e).prod_factor l).tsum_prod
  exact he.symm.trans hs.tsum_eq

theorem probeIdealRawLocalAtUnit_eq (P : HeightOneSpectrum (𝓞 K))
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (hchar : ringChar ((𝓞 K) ⧸ P.asIdeal) ≠ 2)
    (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) (η a b V : ℂ)
    (hV : ‖V‖ < 1) (hb : ‖b‖ < 1)
    (hE : ‖(probeIdealGaussLocalVartheta K P χ η) ^ 6 *
      (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V‖ < 1) :
    probeIdealRawLocalSeries K P χ η (χ u) a b V =
      ArtinMatthews.probeGoodLocalFactor (Ideal.absNorm (P.asIdeal)) V (χ u * b)
        (η * (χ u)⁻¹ * a)
        ((probeIdealGaussLocalVartheta K P χ η) ^ 6 *
          (Ideal.absNorm (P.asIdeal) : ℂ) ^ 4 * a ^ 6 * V) := by
  have h6 : χ ^ 6 = 1 := (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ])
  have hθ : (χ u) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe, h6, MulChar.one_apply_coe]
  have hnorm : ‖χ u‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
    rw [← norm_pow, hθ, norm_one]
  apply probeIdealRawLocalSeries_eq K P χ hχ hminus hchar η (χ u) a b V hθ hV _ hE
  rwa [norm_mul, hnorm, one_mul]

end

end ArtinMatthews.VaryingKummerAnalytic
