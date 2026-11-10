module

public import ArtinMatthews.SourceProductUnits
public import ArtinMatthews.QuotientUnitNormalization
public import ArtinMatthews.SourcePowerWeightMultiplication
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source change d=(hp/Ap)d', v=(sp*Ap/hp)v'.
All three factors are required only to avoid the local prime. Their
quotient units, phase cancellation, and weight factors are derived. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceLocalKernel_unit_change (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (k t J : ℕ)
    (sp ap hp : PrincipalIntegerRing S₀)
    (hsp : sp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hap : ap ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
    (hhp : hp ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    let s := sourceProductUnit S₀ P hP a ha k t sp hsp
    let b := sourceProductUnit S₀ P hP a ha k t ap hap
    let c := sourceProductUnit S₀ P hP a ha k t hp hhp
    let I := primePowerIdeal S₀ P k
    let L := primePowerIdeal S₀ P t
    let W := sourceLocalPowerWeight S₀ P hP a ha χ k
    let Z := sourceLocalPowerWeight S₀ P hP a ha χ t
    let φ := sourceLocalProductPhase S₀ P a ha k t
    quotientCongruenceKernel I L (a ^ t * ap) (a ^ J * hp)
        (φ.mulShift (((s * b)⁻¹ : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) :
          (PrincipalIntegerRing S₀) ⧸ (I * L))) W Z =
      W (quotientUnitProjection (Ideal.mul_le_left : I * L ≤ I) (c * b⁻¹)) *
        Z (quotientUnitProjection (Ideal.mul_le_right : I * L ≤ L) (s * b * c⁻¹)) *
        quotientCongruenceKernel I L (a ^ t) (a ^ J) φ W Z := by
  let I := primePowerIdeal S₀ P k
  let L := primePowerIdeal S₀ P t
  let s := sourceProductUnit S₀ P hP a ha k t sp hsp
  let b := sourceProductUnit S₀ P hP a ha k t ap hap
  let c := sourceProductUnit S₀ P hP a ha k t hp hhp
  let φ := sourceLocalProductPhase S₀ P a ha k t
  let ψ := φ.mulShift (((s * b)⁻¹ : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) :
    (PrincipalIntegerRing S₀) ⧸ (I * L))
  have hAJ : a ^ t * ap ∈ L := by
    dsimp only [L]
    rw [primePowerIdeal, generator_power_ideal S₀ P a ha t, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have hH : Ideal.Quotient.mk (I * L) (a ^ J * hp) =
      (c : (PrincipalIntegerRing S₀) ⧸ (I * L)) * Ideal.Quotient.mk _ (a ^ J) := by
    rw [map_mul, sourceProductUnit_val]
    exact mul_comm _ _
  have hA : Ideal.Quotient.mk (I * L) (a ^ t * ap) *
      ((c * b⁻¹ : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) :
        (PrincipalIntegerRing S₀) ⧸ (I * L)) =
      (c : (PrincipalIntegerRing S₀) ⧸ (I * L)) * Ideal.Quotient.mk _ (a ^ t) := by
    rw [map_mul]
    have hb : (b : (PrincipalIntegerRing S₀) ⧸ (I * L)) = Ideal.Quotient.mk _ ap :=
      sourceProductUnit_val S₀ P hP a ha k t ap hap
    rw [← hb]
    change _ * (b : (PrincipalIntegerRing S₀) ⧸ (I * L)) *
      ((c : (PrincipalIntegerRing S₀) ⧸ (I * L)) *
        ((b⁻¹ : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) : (PrincipalIntegerRing S₀) ⧸ (I * L))) = _
    calc
      _ = (c : (PrincipalIntegerRing S₀) ⧸ (I * L)) * Ideal.Quotient.mk _ (a ^ t) *
          ((b : (PrincipalIntegerRing S₀) ⧸ (I * L)) *
            ((b⁻¹ : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) : (PrincipalIntegerRing S₀) ⧸ (I * L))) := by ring
      _ = _ := by rw [b.mul_inv, mul_one]
  have hCV : c * (s * b * c⁻¹) = s * b := by
    calc
      _ = s * b * (c * c⁻¹) := by
        rw [← mul_assoc c (s * b) c⁻¹, mul_comm c (s * b), mul_assoc]
      _ = s * b := by rw [mul_inv_cancel, mul_one]
  have hphase : ψ.mulShift ((c * (s * b * c⁻¹) : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) :
      (PrincipalIntegerRing S₀) ⧸ (I * L)) = φ := by
    rw [hCV]
    ext x
    change φ ((((s * b)⁻¹ : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) : (PrincipalIntegerRing S₀) ⧸ (I * L)) *
      (((s * b : ((PrincipalIntegerRing S₀) ⧸ (I * L))ˣ) : (PrincipalIntegerRing S₀) ⧸ (I * L)) * x)) = φ x
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have he := quotientCongruenceKernel_unit_change I L (a ^ t * ap) (a ^ J * hp) (a ^ t) (a ^ J)
    hAJ c (c * b⁻¹) (s * b * c⁻¹) hH hA ψ
    (sourceLocalPowerWeight S₀ P hP a ha χ k) (sourceLocalPowerWeight S₀ P hP a ha χ t)
    (sourceLocalPowerWeight S₀ P hP a ha χ k (quotientUnitProjection (Ideal.mul_le_left : I * L ≤ I) (c * b⁻¹)))
    (sourceLocalPowerWeight S₀ P hP a ha χ t (quotientUnitProjection (Ideal.mul_le_right : I * L ≤ L) (s * b * c⁻¹)))
    (fun d => sourceLocalPowerWeight_mul S₀ P hP a ha χ k _ d)
    (fun v => sourceLocalPowerWeight_mul S₀ P hP a ha χ t _ v)
  rw [hphase] at he
  exact he

end
end ArtinMatthews.SourceCRTNormalization
