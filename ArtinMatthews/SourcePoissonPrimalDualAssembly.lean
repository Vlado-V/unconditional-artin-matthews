module

public import ArtinMatthews.SourcePoissonNestedDual
public import ArtinMatthews.SourcePoissonPrimalExpansion
public import ArtinMatthews.SourcePrimeNormSummability
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "C" => ReflectionSquarefreeExponents F S₀
local notation "H" => SourceNonzeroFrequency F S₀

def sourcePoissonFiniteDualValue (X : ℝ) (t : SNormOne F S)
    (s A : E) (h : R) : ℂ :=
  sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A h *
    sourcePoissonNestedDualTransform F S₀ hζ X t s A h

theorem sourcePoissonFiniteDualValue_zero (X : ℝ) (t : SNormOne F S) (s A : E) :
    sourcePoissonFiniteDualValue F S₀ hζ X t s A 0 = 0 := by
  rw [sourcePoissonFiniteDualValue, sourcePoissonNestedDualTransform_zero, mul_zero]

theorem sourcePoissonFiniteDualValue_tsum_nonzero (X : ℝ) (t : SNormOne F S) (s A : E) :
    (∑' h : R, sourcePoissonFiniteDualValue F S₀ hζ X t s A h) =
      ∑' h : H, sourcePoissonFiniteDualValue F S₀ hζ X t s A h.val := by
  symm
  apply tsum_subtype_eq_of_support_subset
  intro h hh hzero
  exact hh (hzero ▸ sourcePoissonFiniteDualValue_zero F S₀ hζ X t s A)

/-- Collect the literal finite Poisson blocks, retaining all the original
source factors and deleting only the proved zero-frequency term. -/
theorem sourcePoissonPrimalExpandedDensity_eq_nestedDual_of_blocks
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X : ℝ} (hX : 0 < X) (Y Z : ℝ) (t : SNormOne F S)
    (hBlocks : ∀ s A : E,
      sourcePoissonPrimalBlock F S₀ hζ s A t ((q s : ℝ) * X) =
        ((((q s : ℝ) * X) / ((q s : ℝ) * (q A : ℝ)) : ℝ) : ℂ) *
        (Real.sqrt (q s : ℝ) : ℂ) *
          ∑' h : R, sourcePoissonFiniteDualValue F S₀ hζ X t s A h) :
    sourcePoissonPrimalExpandedDensity F S₀ hζ η hBad X Y Z t =
      sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z t := by
  let D (p : C × E) := sourcePoissonPhysicalGaussianCoefficient F S₀ hζ η hBad p.1 p.2 Z
  let A (p : C × E) := p.1.val + 3 • p.2
  let W (s : E) := sourceProbeW1Complex ((q s : ℝ) / Y)
  let N (s : E) := (Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹
  let P (s : E) (p : C × E) := sourcePoissonPrimalBlock F S₀ hζ s (A p) t ((q s : ℝ) * X)
  have hTerm (s : E) (p : C × E) :
      (Y : ℂ)⁻¹ * W s * N s * (D p * P s p) =
      ∑' h : H, sourcePoissonNestedDualTerm F S₀ hζ hBad η X Y Z t s p.1 p.2 h.val := by
    have hs : 0 < (q s : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ s)
    have hA : 0 < (q (A p) : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ (A p))
    let v := sourcePoissonFiniteDualValue F S₀ hζ X t s (A p)
    let r : ℂ := (((q s : ℝ) * X) / ((q s : ℝ) * (q (A p) : ℝ)) : ℝ)
    let j : ℂ := (Real.sqrt (q s : ℝ) : ℂ)
    let k : ℂ := (Real.sqrt X / (q (A p) : ℝ) : ℝ)
    have hP : P s p = r * j * ∑' h : H, v h.val := by
      rw [show P s p = _ from hBlocks s (A p), sourcePoissonFiniteDualValue_tsum_nonzero]
    have hN : N s * r * j = k := sourcePoissonPhysicalDilationFactor_complex hX hs hA
    have hDistrib :
        (∑' h : H, sourcePoissonNestedDualTerm F S₀ hζ hBad η X Y Z t s p.1 p.2 h.val) =
        ((Y : ℂ)⁻¹ * W s * k * D p) * ∑' h : H, v h.val := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      unfold sourcePoissonNestedDualTerm sourcePoissonNestedDualScalar
      dsimp only [v, W, k, D, A, sourcePoissonFiniteDualValue]
      ac_rfl
    rw [hP, hDistrib]
    calc
      _ = (Y : ℂ)⁻¹ * W s * (N s * r * j) * D p * (∑' h : H, v h.val) := by ac_rfl
      _ = _ := by rw [hN, mul_assoc ((Y : ℂ)⁻¹ * W s * k) (D p)]
  have hOuter (s : E) :
      (Y : ℂ)⁻¹ * (W s * (N s * ∑' p : C × E, D p * P s p)) =
      ∑' p : C × E, ∑' h : H,
        sourcePoissonNestedDualTerm F S₀ hζ hBad η X Y Z t s p.1 p.2 h.val := by
    calc
      _ = ∑' p : C × E, (Y : ℂ)⁻¹ * W s * N s * (D p * P s p) := by
        rw [tsum_mul_left]
        ac_rfl
      _ = _ := tsum_congr (hTerm s)
  unfold sourcePoissonPrimalExpandedDensity sourcePoissonNestedDualDensity
  rw [← tsum_mul_left]
  exact tsum_congr hOuter

end
end ArtinMatthews.SourceEulerAssembly
