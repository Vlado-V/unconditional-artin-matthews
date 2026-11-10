module

public import ArtinMatthews.SixthPrincipalRowNormalized
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Explicit sixth-power orbit reparametrization under the fixed
principal-row normalization. The root change is a genuine permutation,
also on the nonzero elements integral outside S. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def principalRowRootChange (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : Equiv.Perm Kˣ :=
  Equiv.mulLeft ((principalRowNormalizer S hS).root : Kˣ)

theorem principalRowRootChange_valuation (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (r : Kˣ)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    exteriorPrincipalValuation p (principalRowRootChange S hS r) = exteriorPrincipalValuation p r := by
  change exteriorPrincipalValuation p (((principalRowNormalizer S hS).root : Kˣ)*r) = _
  rw [exteriorPrincipalValuation_mul,(principalRowNormalizer S hS).root.property p hp,zero_add]

theorem principalRowOrbit_reparam (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) (r : Kˣ) :
    exteriorBoundedIdealRowUnit S N i * r^6 =
      normalizedExteriorIdealRowUnit S hS N i * (principalRowRootChange S hS r)^6 := by
  change exteriorBoundedIdealRowUnit S N i*r^6 =
    (exteriorBoundedIdealRowUnit S N i / ((principalRowNormalizer S hS).root : Kˣ)^6) *
      (((principalRowNormalizer S hS).root : Kˣ)*r)^6
  rw [mul_pow,← mul_assoc,div_mul_cancel]

abbrev ExteriorIntegralRoot (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  {r : Kˣ // ∀ p, p ∉ S → 0 ≤ exteriorPrincipalValuation p r}

def exteriorIntegralRootMulEquiv (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : exteriorUnitSubgroup S) : Equiv.Perm (ExteriorIntegralRoot S) where
  toFun r := ⟨(u : Kˣ)*r.1,by
    intro p hp
    rw [exteriorPrincipalValuation_mul,u.property p hp,zero_add]
    exact r.2 p hp⟩
  invFun r := ⟨((u⁻¹ : exteriorUnitSubgroup S) : Kˣ)*r.1,by
    intro p hp
    rw [exteriorPrincipalValuation_mul,(u⁻¹ : exteriorUnitSubgroup S).property p hp,zero_add]
    exact r.2 p hp⟩
  left_inv r := by apply Subtype.ext; exact inv_mul_cancel_left (u : Kˣ) r.1
  right_inv r := by apply Subtype.ext; exact mul_inv_cancel_left (u : Kˣ) r.1

def principalRowIntegralRootChange (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : Equiv.Perm (ExteriorIntegralRoot S) :=
  exteriorIntegralRootMulEquiv S (principalRowNormalizer S hS).root

theorem principalRowIntegralOrbit_reparam (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (r : ExteriorIntegralRoot S) :
    exteriorBoundedIdealRowUnit S N i * r.1^6 = normalizedExteriorIdealRowUnit S hS N i *
      (principalRowIntegralRootChange S hS r).1^6 :=
  principalRowOrbit_reparam S hS N i r.1

theorem principalRowOrbit_tsum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (F : Kˣ → ℂ) :
    (∑' r : Kˣ, F (exteriorBoundedIdealRowUnit S N i*r^6)) =
      ∑' r : Kˣ, F (normalizedExteriorIdealRowUnit S hS N i*r^6) := by
  calc
    _ = ∑' r : Kˣ, F (normalizedExteriorIdealRowUnit S hS N i *
        (principalRowRootChange S hS r)^6) :=
      tsum_congr (fun r => congrArg F (principalRowOrbit_reparam S hS N i r))
    _ = _ := (principalRowRootChange S hS).tsum_eq
      (fun r : Kˣ => F (normalizedExteriorIdealRowUnit S hS N i*r^6))

theorem principalRowIntegralOrbit_tsum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (F : Kˣ → ℂ) :
    (∑' r : ExteriorIntegralRoot S, F (exteriorBoundedIdealRowUnit S N i*r.1^6)) =
      ∑' r : ExteriorIntegralRoot S, F (normalizedExteriorIdealRowUnit S hS N i*r.1^6) := by
  calc
    _ = ∑' r : ExteriorIntegralRoot S, F (normalizedExteriorIdealRowUnit S hS N i *
        (principalRowIntegralRootChange S hS r).1^6) :=
      tsum_congr (fun r => congrArg F (principalRowIntegralOrbit_reparam S hS N i r))
    _ = _ := (principalRowIntegralRootChange S hS).tsum_eq
      (fun r : ExteriorIntegralRoot S => F (normalizedExteriorIdealRowUnit S hS N i*r.1^6))

def principalRowFieldRootChange (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) : Equiv.Perm K :=
  Units.mulLeft ((principalRowNormalizer S hS).root : Kˣ)

theorem principalRowFieldOrbit_reparam (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) (r : K) :
    (exteriorBoundedIdealRowUnit S N i : K)*r^6 =
      (normalizedExteriorIdealRowUnit S hS N i : K)*(principalRowFieldRootChange S hS r)^6 := by
  have h : exteriorBoundedIdealRowUnit S N i =
      normalizedExteriorIdealRowUnit S hS N i*((principalRowNormalizer S hS).root : Kˣ)^6 := by
    change _ = (exteriorBoundedIdealRowUnit S N i / ((principalRowNormalizer S hS).root : Kˣ)^6)*_
    rw [div_mul_cancel]
  have hv := congrArg (fun u : Kˣ => (u : K)) h
  simp only [Units.val_mul,Units.val_pow_eq_pow_val] at hv
  change _ = (normalizedExteriorIdealRowUnit S hS N i : K)*
    ((((principalRowNormalizer S hS).root : Kˣ) : K)*r)^6
  rw [hv,mul_pow,mul_assoc]

theorem principalRowFieldOrbit_tsum (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (F : K → ℂ) :
    (∑' r : K, F ((exteriorBoundedIdealRowUnit S N i : K)*r^6)) =
      ∑' r : K, F ((normalizedExteriorIdealRowUnit S hS N i : K)*r^6) := by
  calc
    _ = ∑' r : K, F ((normalizedExteriorIdealRowUnit S hS N i : K)*
        (principalRowFieldRootChange S hS r)^6) :=
      tsum_congr (fun r => congrArg F (principalRowFieldOrbit_reparam S hS N i r))
    _ = _ := (principalRowFieldRootChange S hS).tsum_eq
      (fun r : K => F ((normalizedExteriorIdealRowUnit S hS N i : K)*r^6))

end
end ArtinMatthews
