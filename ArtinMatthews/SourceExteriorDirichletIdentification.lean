module

public import ArtinMatthews.PrincipalAngularGaussian
public import ArtinMatthews.PrincipalAngularResidue
public import ArtinMatthews.SourceExteriorValueEuler
public import ArtinMatthews.SourceFullIdealEuler
public import ArtinMatthews.SourceLocalCorrectionFactorization
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact deletion of the literal finite source set from the full
Dedekind and ray Euler products. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

theorem sourceExteriorValueEuler_delete (a : ProbePrime F → ℂ) (ha : ∀ P, ‖a P‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) (L : ℂ)
    (hL : HasProd (fun P : ProbePrime F => (1 - sourcePrimeEulerRatio F P (a P) s)⁻¹) L) :
    sourceExteriorValueEuler F S₀ (fun P => a P.val) s =
      L * ∏ P ∈ sourceHilbertSet F S₀, (1 - sourcePrimeEulerRatio F P (a P) s) := by
  let S := sourceHilbertSet F S₀
  let f (P : ProbePrime F) := 1 - sourcePrimeEulerRatio F P (a P) s
  let B := ∏ P ∈ S, f P
  let E := sourceExteriorValueEuler F S₀ (fun P => a P.val) s
  have hExt : HasProd (fun P : SourceExteriorPrime F S₀ => (f P.val)⁻¹) E :=
    sourceExteriorValueEuler_hasProd F S₀ (fun P => a P.val) (fun P => ha P.val) s hs
  have hFin : HasProd (fun P : S => (f P.val)⁻¹) (∏ P ∈ S, (f P)⁻¹) :=
    S.hasProd (fun P => (f P)⁻¹)
  have hAll : HasProd (fun P : ProbePrime F => (f P)⁻¹) ((∏ P ∈ S, (f P)⁻¹) * E) :=
    hFin.mul_compl hExt
  have hEq : B⁻¹ * E = L := by
    change (∏ P ∈ S, f P)⁻¹ * E = L
    rw [← Finset.prod_inv_distrib]
    exact hAll.unique hL
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P _ =>
    sourceOneSub_ne_zero_of_norm_lt_one ((sourcePrimeEulerRatio_norm_le_half F P (a P) s
      (ha P) hs.le).trans_lt (by norm_num)))
  change E = L * B
  rw [← hEq, mul_comm B⁻¹ E, mul_assoc, inv_mul_cancel₀ hB, mul_one]

theorem sourceExteriorValueEuler_eq_angularL {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
    (s : ℂ) (hs : 1 < s.re) :
    sourceExteriorValueEuler F S₀ (fun P => η.allCoefficient P.val.asIdeal) s =
      principalAngularExteriorL η (sourceHilbertSet F S₀) s := by
  simpa only [principalAngularExteriorL, principalAngularRayEulerFactor, sourcePrimeEulerRatio] using
    sourceExteriorValueEuler_delete F S₀ (fun P => η.allCoefficient P.asIdeal)
      (fun P => η.allCoefficient_norm_le_one P.asIdeal) s hs _ (sourceFullRayEuler_hasProd F η s hs)

theorem sourceExteriorValueEuler_eq_exteriorZeta (s : ℂ) (hs : 1 < s.re) :
    sourceExteriorValueEuler F S₀ (fun _ => 1) s =
      principalExteriorZeta (sourceHilbertSet F S₀) s := by
  simpa only [principalExteriorZeta, principalZetaEulerFactor, sourcePrimeEulerRatio,
    mixedDedekindZeta_eq F hs, one_mul] using
    sourceExteriorValueEuler_delete F S₀ (fun _ => 1) (fun _ => by simp) s hs _
      (sourceFullDedekindEuler_hasProd F s hs)

end
end ArtinMatthews.SourceEulerAssembly
