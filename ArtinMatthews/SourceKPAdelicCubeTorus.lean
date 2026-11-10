module

public import ArtinMatthews.SourceKPAdelicProjective
public import ArtinMatthews.SourceKPFiniteAdeleTorus
public import ArtinMatthews.SourceKPIdeleAbsoluteNorm
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

/-! The actual normalized adelic torus and its central cube subgroup.
The cube lift is a homomorphism derived from the local cubic symbols.
The central subgroup is the literal image of the cubic center times
the actual cube ideles, with unique coordinates. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicProjectiveDiagonalLift (x : IdeleGroup (𝓞 K) K) : SourceKPAdelicProjective K hζ :=
  (sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K x),
    sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K x))

theorem sourceKPAdelicProjectiveDiagonalLift_projection (x : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveDiagonalLift K hζ x) =
      sourceKPProjectiveDiagonalHom 𝔸[K] x := by
  apply (sourceKPAdelicProjectiveProductEquiv K).injective
  rw [sourceKPAdelicProjectiveProjection_product]
  change (sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K x),
      sourceKPFiniteAdeleProjectiveProjection K hζ
        (sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K x))) =
    (ProjGenLinGroup.map (sourceKPAdeleInfiniteProjection K) (sourceKPProjectiveDiagonalHom 𝔸[K] x),
      ProjGenLinGroup.map (sourceKPAdeleFiniteProjection K) (sourceKPProjectiveDiagonalHom 𝔸[K] x))
  rw [sourceKPFiniteAdeleProjectiveDiagonalLift_projection, sourceKPProjectiveDiagonalHom_map,
    sourceKPProjectiveDiagonalHom_map]
  rfl

theorem sourceKPAdelicProjectiveDiagonalLift_one :
    sourceKPAdelicProjectiveDiagonalLift K hζ 1 = 1 := by
  apply Prod.ext
  · change sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K 1) = 1
    rw [map_one, map_one]
  · change sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K 1) = 1
    rw [map_one, sourceKPFiniteAdeleProjectiveDiagonalLift_one]

theorem sourceKPAdelicProjectiveDiagonalLift_cube_mul_left (x y : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicProjectiveDiagonalLift K hζ (x ^ (3 : ℕ)) * sourceKPAdelicProjectiveDiagonalLift K hζ y =
      sourceKPAdelicProjectiveDiagonalLift K hζ (x ^ (3 : ℕ) * y) := by
  apply Prod.ext
  · change sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K (x ^ (3 : ℕ))) *
        sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K y) =
      sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K (x ^ (3 : ℕ) * y))
    rw [map_mul, map_mul]
  · change sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K (x ^ (3 : ℕ))) *
        sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K y) =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K (x ^ (3 : ℕ) * y))
    rw [map_mul, map_pow, sourceKPFiniteAdeleProjectiveDiagonalLift_cube_mul_left]

theorem sourceKPAdelicProjectiveDiagonalLift_cube_mul_right (x y : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicProjectiveDiagonalLift K hζ x * sourceKPAdelicProjectiveDiagonalLift K hζ (y ^ (3 : ℕ)) =
      sourceKPAdelicProjectiveDiagonalLift K hζ (x * y ^ (3 : ℕ)) := by
  apply Prod.ext
  · change sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K x) *
        sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K (y ^ (3 : ℕ))) =
      sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (sourceKPIdeleInfiniteUnit K (x * y ^ (3 : ℕ)))
    rw [map_mul, map_mul]
  · change sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K x) *
        sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K (y ^ (3 : ℕ))) =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (sourceKPIdeleFiniteUnit K (x * y ^ (3 : ℕ)))
    rw [map_mul, map_pow, sourceKPFiniteAdeleProjectiveDiagonalLift_cube_mul_right]

theorem sourceKPAdelicProjectiveDiagonalLift_cube_commute (x y : IdeleGroup (𝓞 K) K) :
    Commute (sourceKPAdelicProjectiveDiagonalLift K hζ (x ^ (3 : ℕ))) (sourceKPAdelicProjectiveDiagonalLift K hζ y) := by
  change sourceKPAdelicProjectiveDiagonalLift K hζ (x ^ (3 : ℕ)) * sourceKPAdelicProjectiveDiagonalLift K hζ y =
    sourceKPAdelicProjectiveDiagonalLift K hζ y * sourceKPAdelicProjectiveDiagonalLift K hζ (x ^ (3 : ℕ))
  rw [sourceKPAdelicProjectiveDiagonalLift_cube_mul_left, sourceKPAdelicProjectiveDiagonalLift_cube_mul_right,
    mul_comm (x ^ (3 : ℕ)) y]

theorem sourceKPAdelicProjectiveRationalLift_diagonal (x : Kˣ) :
    sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K x) =
      sourceKPAdelicProjectiveDiagonalLift K hζ (IdeleGroup.unitEmbedding (𝓞 K) K x) := by
  apply Prod.ext
  · exact sourceKPProjectiveDiagonalHom_map (algebraMap K (InfiniteAdeleRing K)) x
  · exact sourceKPFiniteAdeleProjectiveRationalLift_diagonal K hζ x

def sourceKPIdeleCubeSubgroup : Subgroup (IdeleGroup (𝓞 K) K) := (powMonoidHom (3 : ℕ)).range

abbrev SourceKPIdeleCubes := sourceKPIdeleCubeSubgroup K

def sourceKPIdeleCube (x : IdeleGroup (𝓞 K) K) : SourceKPIdeleCubes K :=
  ⟨x ^ (3 : ℕ), ⟨x, rfl⟩⟩

def sourceKPAdelicCubeLift : SourceKPIdeleCubes K →* SourceKPAdelicProjective K hζ where
  toFun x := sourceKPAdelicProjectiveDiagonalLift K hζ x.val
  map_one' := sourceKPAdelicProjectiveDiagonalLift_one K hζ
  map_mul' x y := by
    obtain ⟨a, ha⟩ := x.property
    change a ^ (3 : ℕ) = x.val at ha
    change sourceKPAdelicProjectiveDiagonalLift K hζ (x.val * y.val) =
      sourceKPAdelicProjectiveDiagonalLift K hζ x.val * sourceKPAdelicProjectiveDiagonalLift K hζ y.val
    rw [← ha, sourceKPAdelicProjectiveDiagonalLift_cube_mul_left]

def sourceKPAdelicCubeEmbedding : rootsOfUnity 3 K × SourceKPIdeleCubes K →* SourceKPAdelicProjective K hζ where
  toFun x := sourceKPAdelicProjectiveCenter K hζ x.1 * sourceKPAdelicCubeLift K hζ x.2
  map_one' := by
    change sourceKPAdelicProjectiveCenter K hζ 1 * sourceKPAdelicCubeLift K hζ 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' x y := by
    change sourceKPAdelicProjectiveCenter K hζ (x.1 * y.1) * sourceKPAdelicCubeLift K hζ (x.2 * y.2) = _
    rw [map_mul, map_mul]
    exact (sourceKPAdelicProjectiveCenter_commute K hζ y.1 (sourceKPAdelicCubeLift K hζ x.2)).mul_mul_mul_comm _ _

theorem sourceKPAdelicProjectiveCenter_projection_one (z : rootsOfUnity 3 K) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveCenter K hζ z) = 1 := by
  change sourceKPAdelicProjectiveCenter K hζ z ∈ (sourceKPAdelicProjectiveProjection K hζ).ker
  rw [← sourceKPAdelicProjective_exact K hζ]
  exact ⟨z, rfl⟩

theorem sourceKPAdelicCubeEmbedding_projection (p : rootsOfUnity 3 K × SourceKPIdeleCubes K) :
    sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicCubeEmbedding K hζ p) = sourceKPProjectiveDiagonalHom 𝔸[K] p.2.val := by
  change sourceKPAdelicProjectiveProjection K hζ
      (sourceKPAdelicProjectiveCenter K hζ p.1 * sourceKPAdelicProjectiveDiagonalLift K hζ p.2.val) = _
  rw [map_mul, sourceKPAdelicProjectiveCenter_projection_one, one_mul, sourceKPAdelicProjectiveDiagonalLift_projection]

theorem sourceKPAdelicCubeEmbedding_injective : Function.Injective (sourceKPAdelicCubeEmbedding K hζ) := by
  intro x y h
  have hp := congrArg (sourceKPAdelicProjectiveProjection K hζ) h
  rw [sourceKPAdelicCubeEmbedding_projection, sourceKPAdelicCubeEmbedding_projection] at hp
  have he : x.2 = y.2 := Subtype.ext (sourceKPProjectiveDiagonalHom_injective 𝔸[K] hp)
  change sourceKPAdelicProjectiveCenter K hζ x.1 * sourceKPAdelicCubeLift K hζ x.2 =
    sourceKPAdelicProjectiveCenter K hζ y.1 * sourceKPAdelicCubeLift K hζ y.2 at h
  rw [he] at h
  exact Prod.ext (sourceKPAdelicProjectiveCenter_injective K hζ (mul_right_cancel h)) he

def sourceKPAdelicCubeTorus : Subgroup (SourceKPAdelicProjective K hζ) := (sourceKPAdelicCubeEmbedding K hζ).range

def sourceKPAdelicCubeTorusEquiv : rootsOfUnity 3 K × SourceKPIdeleCubes K ≃* sourceKPAdelicCubeTorus K hζ := by
  let m := sourceKPAdelicCubeEmbedding K hζ
  let f := m.codRestrict m.range (fun p => ⟨p, rfl⟩)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y he
    exact sourceKPAdelicCubeEmbedding_injective K hζ (congrArg Subtype.val he)
  · rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩

theorem sourceKPAdelicCubeTorusEquiv_val (p : rootsOfUnity 3 K × SourceKPIdeleCubes K) :
    (sourceKPAdelicCubeTorusEquiv K hζ p).val = sourceKPAdelicCubeEmbedding K hζ p := rfl

end
end ArtinMatthews
