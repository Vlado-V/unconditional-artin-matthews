module

public import ArtinMatthews.SLocalNormAlgebra
public import ArtinMatthews.SLocalSixthCompactReduction
public import ArtinMatthews.SLocalPositiveScaling
public import ArtinMatthews.AllowedGeneratorPowerAdjustment
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Actual allowed generators can be selected in a single fixed
compact norm-one S-local set after the literal source scaling.
The correction is a sixth power of an actual S-unit. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain SUnitGroup FractionalIdeal
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem exists_balanced_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    ∃ a : Kˣ, toPrincipalIdeal (sourceRing K S₀) K a = I ∧
      a ∈ allowedSubgroup K hζ S₀ ∧
      sWholeDiagonal K (sourceHilbertSet K S₀) a /
        sLocalPositiveScaling K hζ (sourceHilbertSet K S₀) (idealSNorm K hζ S₀ I) ∈
          sixthBalancedCompactSet K (sourceHilbertSet K S₀) := by
  let S := sourceHilbertSet K S₀
  let g := generator K hζ S₀ I
  let q := idealSNorm K hζ S₀ I
  let l := sLocalPositiveScaling K hζ S q
  have hq : 0 < q := idealSNorm_pos K hζ S₀ I
  have hg : sLocalNorm K S (sWholeDiagonal K S g) = q := rfl
  have hl : sLocalNorm K S l = q := sLocalPositiveScaling_norm K hζ S hq
  have hnorm : sLocalNorm K S (sWholeDiagonal K S g / l) = 1 := by
    rw [sLocalNorm_div, hg, hl, div_self hq.ne']
  obtain ⟨u, hu⟩ := exists_sUnit_sixth_compact_reduction K S (sWholeDiagonal K S g / l) hnorm
  refine ⟨g * (u : Kˣ) ^ 6, ?_, ?_, ?_⟩
  · exact (adjust_sixth_preserves_ideal K S₀ g u).trans (generator_principal K hζ S₀ I)
  · exact adjust_sixth_preserves_allowed K hζ S₀ g (generator_allowed K hζ S₀ I) u
  · change sWholeDiagonal K S (g * (u : Kˣ) ^ 6) / l ∈ sixthBalancedCompactSet K S
    rw [map_mul, ← div_mul_eq_mul_div]
    exact hu

def balancedGenerator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) : Kˣ :=
  (exists_balanced_generator K hζ S₀ I).choose

theorem balancedGenerator_principal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    toPrincipalIdeal (sourceRing K S₀) K (balancedGenerator K hζ S₀ I) = I :=
  (exists_balanced_generator K hζ S₀ I).choose_spec.1

theorem balancedGenerator_allowed {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    balancedGenerator K hζ S₀ I ∈ allowedSubgroup K hζ S₀ :=
  (exists_balanced_generator K hζ S₀ I).choose_spec.2.1

theorem balancedGenerator_compact {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    sWholeDiagonal K (sourceHilbertSet K S₀) (balancedGenerator K hζ S₀ I) /
      sLocalPositiveScaling K hζ (sourceHilbertSet K S₀) (idealSNorm K hζ S₀ I) ∈
        sixthBalancedCompactSet K (sourceHilbertSet K S₀) :=
  (exists_balanced_generator K hζ S₀ I).choose_spec.2.2

theorem balancedGenerator_mul_ratio_sixth {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I J : idealGroup K S₀) :
    ∃ u : SUnitGroup (K := K) (sourceHilbertSet K S₀),
      balancedGenerator K hζ S₀ (I * J) /
        (balancedGenerator K hζ S₀ I * balancedGenerator K hζ S₀ J) = (u : Kˣ) ^ 6 := by
  apply allowed_ratio_sixth K hζ S₀ _ _ (balancedGenerator_allowed K hζ S₀ _)
    ((allowedSubgroup K hζ S₀).mul_mem (balancedGenerator_allowed K hζ S₀ I)
      (balancedGenerator_allowed K hζ S₀ J))
  rw [map_mul, balancedGenerator_principal, balancedGenerator_principal, balancedGenerator_principal]

theorem balancedGenerator_norm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    fieldSNorm K (sourceHilbertSet K S₀) (balancedGenerator K hζ S₀ I) = idealSNorm K hζ S₀ I :=
  (idealSNorm_eq_of_generator K hζ S₀ I _ (balancedGenerator_principal K hζ S₀ I)).symm

end
end ArtinMatthews.AllowedGenerators
