module

public import ArtinMatthews.SourcePoissonAdditiveMass
public import ArtinMatthews.SourceReducedFractionTraceLift
public import ArtinMatthews.SourcePoissonReducedResidues
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
open SIntegerFourier SourcePhysical StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "OS" => PrincipalIntegerRing (sourceHilbertSeed F S₀)
local notation "E" => SourcePrimeExponents F S₀
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : E → OS)
local notation "ha" => sourcePrimeExponentGenerator_ne_zero F hζ S₀
local notation "U" e => (OS ⧸ (Ideal.span {a e} : Ideal OS))ˣ

/-- The exact original Gauss sum is supported on reduced residues.
The modulus-one term stays in the sum with its single quotient unit. -/
theorem sourcePoissonOriginalGauss_eq_sum_units (e : E) (m : OS) :
    letI := sourcePoissonQuotientUnitFintype F S₀ hζ e
    sourcePoissonOriginalGauss F S₀ hζ e m =
      ∑ d : U e, sourcePoissonQuotientResidue F S₀ hζ e d.val *
        sourceReducedFractionPhase F S₀ a ha ⟨e, d⟩ m := by
  let I : Ideal OS := Ideal.span {a e}
  let : Finite (OS ⧸ I) := sourcePrimeExponentGenerator_quotient_finite F hζ S₀ e
  let : Fintype (OS ⧸ I) := Fintype.ofFinite _
  let := sourcePoissonQuotientUnitFintype F S₀ hζ e
  let ψ : AddChar (OS ⧸ I) ℂ :=
    sIntegerQuotientPhase F (sourceHilbertSet F S₀) (a e) (ha e)
  let f (d : OS ⧸ I) : ℂ :=
    sourcePoissonQuotientResidue F S₀ hζ e d * ψ (Ideal.Quotient.mk I m * d)
  let i : (U e) ↪ (OS ⧸ I) := ⟨Units.val, Units.val_injective⟩
  change (∑' d : OS ⧸ I, f d) = ∑ d : U e, f (i d)
  rw [tsum_fintype, ← Finset.sum_map]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  have hnu : ¬ IsUnit d := by
    rintro ⟨u, hu⟩
    exact hd (Finset.mem_map.mpr ⟨u, Finset.mem_univ _, hu⟩)
  exact mul_eq_zero_of_left (sourcePoissonQuotientResidue_eq_zero_of_nonunit F S₀ hζ e d hnu) _

end
end ArtinMatthews.SourceEulerAssembly
