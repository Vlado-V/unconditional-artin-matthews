module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual fractional-ideal membership in terms of every normalized
finite valuation. This turns the finite local ball conditions into a
genuine fractional-ideal lattice without assuming the correspondence. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K

theorem sourceFractionalIdeal_le_one_of_counts (I : FI) (hI : I ≠ 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K P I) : I ≤ 1 := by
  let f (P : HeightOneSpectrum (𝓞 K)) : FI := (P.asIdeal : FI) ^ FractionalIdeal.count K P I
  have hf : Function.HasFiniteMulSupport f := by
    apply (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset
    intro P hP hz
    exact hP (by simp only [f, hz, zpow_zero])
  have hg : Function.HasFiniteMulSupport (fun _ : HeightOneSpectrum (𝓞 K) => (1 : FI)) := by
    exact Function.hasFiniteMulSupport_one
  have hle (P : HeightOneSpectrum (𝓞 K)) : f P ≤ 1 := by
    let e := FractionalIdeal.count K P I
    have he : (e.toNat : ℤ) = e := Int.toNat_of_nonneg (h P)
    change (P.asIdeal : FI) ^ e ≤ 1
    rw [← he, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_top]
    exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr le_top
  calc
    I = ∏ᶠ P, f P := (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
    _ ≤ ∏ᶠ _ : HeightOneSpectrum (𝓞 K), (1 : FI) := finprod_le_finprod hf hg hle
    _ = 1 := finprod_one

theorem sourceFractionalIdeal_le_iff_counts (I J : FI) (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ P : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K P J ≤ FractionalIdeal.count K P I := by
  constructor
  · intro h P
    exact FractionalIdeal.count_mono K P hI h
  · intro h
    have hL : I * J⁻¹ ≤ 1 := sourceFractionalIdeal_le_one_of_counts K _
      (mul_ne_zero hI (inv_ne_zero hJ)) (by
        intro P
        rw [FractionalIdeal.count_mul K P hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
        linarith [h P])
    have ht := mul_le_mul_right hL J
    simpa only [mul_left_comm J I J⁻¹, mul_inv_cancel₀ hJ, mul_one] using ht

theorem sourceFractionalIdeal_mem_iff_valuation (I : FI) (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ P : HeightOneSpectrum (𝓞 K),
      P.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K P I) := by
  by_cases hx : x = 0
  · subst x
    simp
    exact I.zero_mem
  let a := Units.mk0 x hx
  let J : FI := toPrincipalIdeal (𝓞 K) K a
  have hJ : J ≠ 0 := (toPrincipalIdeal (𝓞 K) K a).ne_zero
  have hmem : x ∈ I ↔ J ≤ I := by
    change x ∈ I ↔ (toPrincipalIdeal (𝓞 K) K a : FI) ≤ I
    rw [coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.spanSingleton_le_iff_mem]
  rw [hmem, sourceFractionalIdeal_le_iff_counts K J I hJ hI]
  have hc (P : HeightOneSpectrum (𝓞 K)) : FractionalIdeal.count K P J =
      -WithZero.log (P.valuation K x) := IdeleGroup.count_toPrincipalIdeal a P
  constructor
  · intro h P
    have hp := h P
    rw [hc P] at hp
    exact WithZero.le_exp_of_log_le (by omega)
  · intro h P
    rw [hc P]
    have hv : P.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    have he := (WithZero.log_le_iff_le_exp hv).mpr (h P)
    omega

end
end ArtinMatthews.SourcePhysical
