module

public import ArtinMatthews.SourceQuadraticClassFactorization
public import ArtinMatthews.SourceQuadraticCommonGram
public import ArtinMatthews.SourceQuadraticConductor
public import ArtinMatthews.SourceQuadraticPairConductor
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

/-! Original class-sliced common pairs inherit the exact residual conductor. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀

theorem sourceQuadraticClassPair_mem {G : Type*} [DecidableEq G]
    (cols : Finset E) (label : E → G) (κ : G) (p : E × E) (g : E)
    (hp : p ∈ ((sourceQuadraticClassColumns F S₀ cols label κ) ×ˢ
        (sourceQuadraticClassColumns F S₀ cols label κ)).filter
      (fun p : E × E => p.1 ⊓ p.2 = g)) :
    p.1 ∈ cols ∧ p.2 ∈ cols ∧ p.1 ⊓ p.2 = g ∧ label p.1 = label p.2 := by
  obtain ⟨hpair, hg⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hpair
  obtain ⟨hb, hbκ⟩ := Finset.mem_filter.mp hb
  obtain ⟨hc, hcκ⟩ := Finset.mem_filter.mp hc
  exact ⟨hb, hc, hg, hbκ.trans hcκ.symm⟩

theorem sourceQuadraticClassPair_local_conductor
    (cols : Finset E) (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (κ : SLocalPowerClasses F 2 (sourceHilbertSet F S₀)) (p : E × E) (g : E)
    (hp : p ∈ ((sourceQuadraticClassColumns F S₀ cols
        (sourceQuadraticLocalClass F S₀ hζ) κ) ×ˢ
        (sourceQuadraticClassColumns F S₀ cols (sourceQuadraticLocalClass F S₀ hζ) κ)).filter
      (fun p : E × E => p.1 ⊓ p.2 = g)) :
    sourceReflectionIsSquarefree ((p.1 - g) + (p.2 - g)) ∧
      sourceQuadraticLocalClass F S₀ hζ (p.1 - g) =
        sourceQuadraticLocalClass F S₀ hζ (p.2 - g) ∧
      sourceQuadraticConductor F S₀ hζ ((p.1 - g) + (p.2 - g)) =
        I (p.1 - g) * I (p.2 - g) := by
  obtain ⟨hb, hc, hg, hclass⟩ := sourceQuadraticClassPair_mem F S₀ cols _ κ p g hp
  exact ⟨(sourceQuadraticPair_residual_data F S₀ _ _ _ (hcols _ hb) (hcols _ hc) hg).2.2.2,
    sourceQuadraticPair_residual_localClass F S₀ hζ _ _ _ hg hclass,
    sourceQuadraticPairConductor_eq_product F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc) hg hclass⟩

theorem sourceQuadraticClassPair_ray_conductor
    (cols : Finset E) (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (κ : SourceQuadraticRayClass F S₀) (p : E × E) (g : E)
    (hp : p ∈ ((sourceQuadraticClassColumns F S₀ cols
        (sourcePrimeExponentRayClass F S₀) κ) ×ˢ
        (sourceQuadraticClassColumns F S₀ cols (sourcePrimeExponentRayClass F S₀) κ)).filter
      (fun p : E × E => p.1 ⊓ p.2 = g)) :
    sourceReflectionIsSquarefree ((p.1 - g) + (p.2 - g)) ∧
      sourceQuadraticLocalClass F S₀ hζ (p.1 - g) =
        sourceQuadraticLocalClass F S₀ hζ (p.2 - g) ∧
      sourceQuadraticConductor F S₀ hζ ((p.1 - g) + (p.2 - g)) =
        I (p.1 - g) * I (p.2 - g) := by
  obtain ⟨hb, hc, hg, hclass⟩ := sourceQuadraticClassPair_mem F S₀ cols _ κ p g hp
  have hlocal := sourcePrimeExponentRayClass_eq_localClass F S₀ hζ p.1 p.2 hclass
  exact ⟨(sourceQuadraticPair_residual_data F S₀ _ _ _ (hcols _ hb) (hcols _ hc) hg).2.2.2,
    sourceQuadraticPair_residual_localClass F S₀ hζ _ _ _ hg hlocal,
    sourceQuadraticPairConductor_eq_product F S₀ hζ _ _ _ (hcols _ hb) (hcols _ hc) hg hlocal⟩

end
end ArtinMatthews.SourceEulerAssembly
