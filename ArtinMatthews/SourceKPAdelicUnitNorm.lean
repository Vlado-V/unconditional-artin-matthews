module

public import ArtinMatthews.SourceKPAdelicPrincipalSeries
public import ArtinMatthews.SourceKPAdelicUnitSpherical
public import ArtinMatthews.SourceKPAdelicDiagonalCharacter
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

/-! The exact norm of the actual unit-torus-fixed inducing vector on
its support, and the normalized Borel bound supplied by this vector. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicCentralComplex_norm (z : rootsOfUnity 3 K) :
    ‖(sourceKPAdelicCentralComplex K hζ z : ℂ)‖ = 1 := by
  have hz : z^(3 : ℕ) = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 z.val).mp z.property
  have hc := congrArg (fun w : rootsOfUnity 3 K => (sourceKPAdelicCentralComplex K hζ w : ℂ)) hz
  have hp : (sourceKPAdelicCentralComplex K hζ z : ℂ)^3 = 1 := by
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using hc
  exact Complex.norm_eq_one_of_pow_eq_one hp (by decide)

theorem sourceKPAdelicTorusInducingCharacter_norm (s : ℂ)
    (h : sourceKPAdelicTorusInducingSubgroup K hζ) :
    ‖(sourceKPAdelicTorusInducingCharacter K hζ s h : ℂ)‖ =
      (sourceKPIdeleAbsoluteNorm K (sourceKPAdelicTorusIdele K hζ h.val)) ^ s.re := by
  obtain ⟨⟨b,y⟩, hp⟩ := h.property
  change sourceKPAdelicRationalCubeJoin K hζ (b,y) = h.val.val at hp
  obtain ⟨⟨z,c⟩, hq⟩ := (sourceKPAdelicCubeTorusEquiv K hζ).surjective b
  have hc : sourceKPAdelicTorusInducingCharacter K hζ s h =
      sourceKPAdelicCentralComplex K hζ z * sourceKPIdeleComplexNorm K s c.val := by
    change sourceKPAdelicParametricRationalCharacter K hζ s
      (⟨h.val.val, h.property⟩ : sourceKPAdelicRationalCubeTorus K hζ) = _
    have he : (⟨sourceKPAdelicRationalCubeJoin K hζ (b,y), ⟨(b,y),rfl⟩⟩ :
        sourceKPAdelicRationalCubeTorus K hζ) = ⟨h.val.val,h.property⟩ := Subtype.ext hp
    rw [← he, sourceKPAdelicParametricRationalCharacter_join, ← hq,
      sourceKPAdelicParametricCharacter_equiv]
  have ha : sourceKPAdelicTorusIdele K hζ h.val =
      c.val * IdeleGroup.unitEmbedding (𝓞 K) K y := by
    apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
    rw [← sourceKPAdelicTorusIdele_projection]
    rw [← hp, ← hq, sourceKPAdelicCubeRational_join_factor, map_mul,
      sourceKPAdelicProjectiveCenter_projection_one, one_mul,
      sourceKPAdelicProjectiveDiagonalLift_projection]
  rw [hc, Units.val_mul, norm_mul, sourceKPAdelicCentralComplex_norm, one_mul,
    sourceKPIdeleComplexNorm_norm, ha, map_mul, sourceKPIdeleAbsoluteNorm_principal, mul_one]

theorem sourceKPAdelicUnitTorus_ideleNorm (u : sourceKPAdelicUnitTorus K hζ) :
    sourceKPIdeleAbsoluteNorm K (sourceKPAdelicTorusIdele K hζ u.val) = 1 := by
  obtain ⟨a,ha⟩ := sourceKPAdelicUnitTorus_mem K hζ u
  have he : sourceKPAdelicTorusIdele K hζ u.val = a.val := by
    apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
    rw [← sourceKPAdelicTorusIdele_projection, ha,
      sourceKPAdelicProjectiveDiagonalLift_projection]
  rw [he]
  exact sourceKPAdelicUnitIdeles_norm K a

theorem sourceKPAdelicUnitSphericalVector_norm_factorable (s : ℂ)
    (t : sourceKPAdelicCoveringTorus K hζ)
    (ht : sourceKPAdelicUnitFactorable K hζ t) :
    ‖(sourceKPAdelicUnitSphericalVector K hζ s).val t‖ =
      (sourceKPIdeleAbsoluteNorm K (sourceKPAdelicTorusIdele K hζ t)) ^ s.re := by
  obtain ⟨h,u,he⟩ := ht
  change ‖sourceKPAdelicUnitSectionValue K hζ s t‖ = _
  rw [sourceKPAdelicUnitSectionValue_factor K hζ s t h u he,
    sourceKPAdelicTorusInducingCharacter_norm, he, map_mul, map_mul,
    sourceKPAdelicUnitTorus_ideleNorm, mul_one]

theorem sourceKPAdelicUnitSphericalVector_norm_le (s : ℂ)
    (t : sourceKPAdelicCoveringTorus K hζ) :
    ‖(sourceKPAdelicUnitSphericalVector K hζ s).val t‖ ≤
      (sourceKPIdeleAbsoluteNorm K (sourceKPAdelicTorusIdele K hζ t)) ^ s.re := by
  by_cases ht : sourceKPAdelicUnitFactorable K hζ t
  · exact (sourceKPAdelicUnitSphericalVector_norm_factorable K hζ s t ht).le
  · change ‖sourceKPAdelicUnitSectionValue K hζ s t‖ ≤ _
    rw [sourceKPAdelicUnitSectionValue_zero K hζ s t ht, norm_zero]
    exact Real.rpow_nonneg (sourceKPIdeleAbsoluteNorm_pos K _).le _

theorem sourceKPAdelicBorelModularHalf_norm (b : sourceKPAdelicCoveringBorel K hζ) :
    ‖sourceKPAdelicBorelModularHalf K hζ b‖ =
      (sourceKPIdeleAbsoluteNorm K
        (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b))) ^ (1/2 : ℝ) := by
  change ‖(sourceKPIdeleComplexNorm K (1/2 : ℂ)
    (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b)) : ℂ)‖ = _
  rw [sourceKPIdeleComplexNorm_norm]
  norm_num

theorem sourceKPAdelicUnitSphericalVector_normalizedBorel_bound (s : ℂ)
    (b : sourceKPAdelicCoveringBorel K hζ) :
    ‖(sourceKPAdelicNormalizedBorelRepresentation K hζ s b
      (sourceKPAdelicUnitSphericalVector K hζ s)).val 1‖ ≤
      (sourceKPIdeleAbsoluteNorm K
        (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b))) ^
          (s.re+1/2) := by
  change ‖sourceKPAdelicBorelModularHalf K hζ b *
    (sourceKPAdelicUnitSphericalVector K hζ s).val
      (1 * sourceKPAdelicBorelTorusProjection K hζ b)‖ ≤ _
  rw [one_mul, norm_mul]
  calc
    _ ≤ ‖sourceKPAdelicBorelModularHalf K hζ b‖ *
        (sourceKPIdeleAbsoluteNorm K
          (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b))) ^ s.re :=
      mul_le_mul_of_nonneg_left (sourceKPAdelicUnitSphericalVector_norm_le K hζ s _)
        (norm_nonneg _)
    _ = _ := by
      rw [sourceKPAdelicBorelModularHalf_norm, ← Real.rpow_add (sourceKPIdeleAbsoluteNorm_pos K _)]
      congr 1
      ring

end
end ArtinMatthews
