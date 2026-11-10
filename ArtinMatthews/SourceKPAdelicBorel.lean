module

public import ArtinMatthews.SourceKPRingBorel
public import ArtinMatthews.SourceKPAdelicCoveringTorus
public import ArtinMatthews.SourceKPAdelicTorusUpper
public import ArtinMatthews.SourceKPAdelicUpperProjection
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

/-! The actual covering Borel over the full adele ring, with unique
upper-root and covering-torus factors. Its torus projection retains
the cubic center and splits the inclusion of the covering torus. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private theorem sourceKPAdelicTorusIdele_exists (t : sourceKPAdelicCoveringTorus K hζ) :
    ∃ a : IdeleGroup (𝓞 K) K,
      sourceKPProjectiveDiagonalHom 𝔸[K] a = sourceKPAdelicProjectiveProjection K hζ t.val :=
  t.property

private def sourceKPAdelicTorusIdeleValue (t : sourceKPAdelicCoveringTorus K hζ) : IdeleGroup (𝓞 K) K :=
  Classical.choose (sourceKPAdelicTorusIdele_exists K hζ t)

private theorem sourceKPAdelicTorusIdeleValue_spec (t : sourceKPAdelicCoveringTorus K hζ) :
    sourceKPProjectiveDiagonalHom 𝔸[K] (sourceKPAdelicTorusIdeleValue K hζ t) =
      sourceKPAdelicProjectiveProjection K hζ t.val :=
  Classical.choose_spec (sourceKPAdelicTorusIdele_exists K hζ t)

def sourceKPAdelicTorusIdele : sourceKPAdelicCoveringTorus K hζ →* IdeleGroup (𝓞 K) K where
  toFun := sourceKPAdelicTorusIdeleValue K hζ
  map_one' := by
    apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
    rw [sourceKPAdelicTorusIdeleValue_spec]
    change sourceKPAdelicProjectiveProjection K hζ 1 = sourceKPProjectiveDiagonalHom 𝔸[K] 1
    rw [map_one, map_one]
  map_mul' t u := by
    apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
    rw [sourceKPAdelicTorusIdeleValue_spec, map_mul,
      sourceKPAdelicTorusIdeleValue_spec, sourceKPAdelicTorusIdeleValue_spec]
    exact map_mul (sourceKPAdelicProjectiveProjection K hζ) t.val u.val

theorem sourceKPAdelicTorusIdele_projection (t : sourceKPAdelicCoveringTorus K hζ) :
    sourceKPAdelicProjectiveProjection K hζ t.val =
      sourceKPProjectiveDiagonalHom 𝔸[K] (sourceKPAdelicTorusIdele K hζ t) :=
  (sourceKPAdelicTorusIdeleValue_spec K hζ t).symm

theorem sourceKPAdelicTorus_upper (t : sourceKPAdelicCoveringTorus K hζ) (x : 𝔸[K]) :
    t.val * sourceKPAdelicUpperLift K hζ x =
      sourceKPAdelicUpperLift K hζ (((sourceKPAdelicTorusIdele K hζ t) : 𝔸[K]) * x) * t.val :=
  sourceKPAdelicTorus_upper_of_projection K hζ t.val _
    (sourceKPAdelicTorusIdele_projection K hζ t) x

def sourceKPAdelicCoveringBorel : Subgroup (SourceKPAdelicProjective K hζ) :=
  (sourceKPRingBorel 𝔸[K]).comap (sourceKPAdelicProjectiveProjection K hζ)

theorem sourceKPAdelicCoveringBorel_upper_mem (x : 𝔸[K]) :
    sourceKPAdelicUpperLift K hζ x ∈ sourceKPAdelicCoveringBorel K hζ := by
  change sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicUpperLift K hζ x) ∈ sourceKPRingBorel 𝔸[K]
  rw [sourceKPAdelicUpperLift_projection, sourceKPRingBorel_mem_iff]
  exact ⟨x, 1, by rw [map_one, mul_one]⟩

theorem sourceKPAdelicCoveringTorus_le_borel :
    sourceKPAdelicCoveringTorus K hζ ≤ sourceKPAdelicCoveringBorel K hζ := by
  intro t ht
  obtain ⟨a, ha⟩ := ht
  change sourceKPAdelicProjectiveProjection K hζ t ∈ sourceKPRingBorel 𝔸[K]
  rw [← ha, sourceKPRingBorel_mem_iff]
  exact ⟨0, a, by rw [sourceKPUpperMatrix_zero, map_one, one_mul]⟩

theorem sourceKPAdelicCoveringBorel_mem_iff (g : SourceKPAdelicProjective K hζ) :
    g ∈ sourceKPAdelicCoveringBorel K hζ ↔
      ∃ (x : 𝔸[K]) (t : sourceKPAdelicCoveringTorus K hζ),
        g = sourceKPAdelicUpperLift K hζ x * t.val := by
  constructor
  · intro hg
    obtain ⟨x, a, ha⟩ := (sourceKPRingBorel_mem_iff 𝔸[K] _).mp hg
    let v := sourceKPAdelicUpperLift K hζ x * sourceKPAdelicProjectiveDiagonalLift K hζ a
    have hv : sourceKPAdelicProjectiveProjection K hζ v =
        sourceKPAdelicProjectiveProjection K hζ g := by
      rw [map_mul, sourceKPAdelicUpperLift_projection,
        sourceKPAdelicProjectiveDiagonalLift_projection, ha]
    have hk : g * v⁻¹ ∈ (sourceKPAdelicProjectiveProjection K hζ).ker := by
      change sourceKPAdelicProjectiveProjection K hζ (g * v⁻¹) = 1
      rw [map_mul, map_inv, hv, mul_inv_cancel]
    rw [← sourceKPAdelicProjective_exact K hζ] at hk
    obtain ⟨z, hz⟩ := hk
    let t : sourceKPAdelicCoveringTorus K hζ :=
      ⟨sourceKPAdelicProjectiveCenter K hζ z * sourceKPAdelicProjectiveDiagonalLift K hζ a,
        (sourceKPAdelicCoveringTorus K hζ).mul_mem
          (sourceKPAdelicCoveringTorus_center_mem K hζ z)
          (sourceKPAdelicCoveringTorus_diagonal_mem K hζ a)⟩
    refine ⟨x, t, ?_⟩
    change g = sourceKPAdelicUpperLift K hζ x *
      (sourceKPAdelicProjectiveCenter K hζ z * sourceKPAdelicProjectiveDiagonalLift K hζ a)
    rw [← mul_assoc, ← (sourceKPAdelicProjectiveCenter_commute K hζ z
      (sourceKPAdelicUpperLift K hζ x)).eq, mul_assoc]
    change g = sourceKPAdelicProjectiveCenter K hζ z * v
    rw [hz, inv_mul_cancel_right]
  · rintro ⟨x, t, rfl⟩
    exact (sourceKPAdelicCoveringBorel K hζ).mul_mem
      (sourceKPAdelicCoveringBorel_upper_mem K hζ x)
      (sourceKPAdelicCoveringTorus_le_borel K hζ t.property)

theorem sourceKPAdelicBorel_coordinates_injective : Function.Injective
    (fun p : 𝔸[K] × sourceKPAdelicCoveringTorus K hζ => sourceKPAdelicUpperLift K hζ p.1 * p.2.val) := by
  rintro ⟨x, t⟩ ⟨y, u⟩ he
  have hp : ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] x) *
      sourceKPProjectiveDiagonalHom 𝔸[K] (sourceKPAdelicTorusIdele K hζ t) =
    ProjGenLinGroup.mk (sourceKPUpperMatrix 𝔸[K] y) *
      sourceKPProjectiveDiagonalHom 𝔸[K] (sourceKPAdelicTorusIdele K hζ u) := by
    have hp := congrArg (sourceKPAdelicProjectiveProjection K hζ) he
    rw [map_mul, map_mul, sourceKPAdelicUpperLift_projection,
      sourceKPAdelicUpperLift_projection, sourceKPAdelicTorusIdele_projection,
      sourceKPAdelicTorusIdele_projection] at hp
    exact hp
  have hc : (x, sourceKPAdelicTorusIdele K hζ t) = (y, sourceKPAdelicTorusIdele K hζ u) := by
    apply sourceKPRingBorel_coordinates_injective 𝔸[K]
    exact hp
  have hxy : x = y := congrArg Prod.fst hc
  have htu : t = u := by
    apply Subtype.ext
    rw [hxy] at he
    exact mul_left_cancel he
  exact Prod.ext hxy htu

def sourceKPAdelicBorelCoordinatesEquiv :
    𝔸[K] × sourceKPAdelicCoveringTorus K hζ ≃ sourceKPAdelicCoveringBorel K hζ :=
  Equiv.ofBijective
    (fun p => ⟨sourceKPAdelicUpperLift K hζ p.1 * p.2.val,
      (sourceKPAdelicCoveringBorel_mem_iff K hζ _).mpr ⟨p.1, p.2, rfl⟩⟩)
    ⟨fun _ _ he => sourceKPAdelicBorel_coordinates_injective K hζ (congrArg Subtype.val he),
      fun b => by
        obtain ⟨x, t, hxt⟩ := (sourceKPAdelicCoveringBorel_mem_iff K hζ b.val).mp b.property
        exact ⟨(x,t), Subtype.ext hxt.symm⟩⟩

theorem sourceKPAdelicBorelCoordinatesEquiv_val (x : 𝔸[K]) (t : sourceKPAdelicCoveringTorus K hζ) :
    (sourceKPAdelicBorelCoordinatesEquiv K hζ (x,t)).val = sourceKPAdelicUpperLift K hζ x * t.val := rfl

theorem sourceKPAdelicBorelCoordinatesEquiv_mul
    (p q : 𝔸[K] × sourceKPAdelicCoveringTorus K hζ) :
    sourceKPAdelicBorelCoordinatesEquiv K hζ p * sourceKPAdelicBorelCoordinatesEquiv K hζ q =
      sourceKPAdelicBorelCoordinatesEquiv K hζ
        (p.1 + (sourceKPAdelicTorusIdele K hζ p.2 : 𝔸[K]) * q.1, p.2*q.2) := by
  apply Subtype.ext
  change (sourceKPAdelicUpperLift K hζ p.1 * p.2.val) *
      (sourceKPAdelicUpperLift K hζ q.1 * q.2.val) =
    sourceKPAdelicUpperLift K hζ
      (p.1 + (sourceKPAdelicTorusIdele K hζ p.2 : 𝔸[K]) * q.1) * (p.2.val*q.2.val)
  rw [sourceKPAdelicUpperLift_add]
  calc
    _ = sourceKPAdelicUpperLift K hζ p.1 *
        (p.2.val * sourceKPAdelicUpperLift K hζ q.1) * q.2.val := by simp only [mul_assoc]
    _ = _ := by rw [sourceKPAdelicTorus_upper]; simp only [mul_assoc]

def sourceKPAdelicBorelTorusProjection :
    sourceKPAdelicCoveringBorel K hζ →* sourceKPAdelicCoveringTorus K hζ where
  toFun b := ((sourceKPAdelicBorelCoordinatesEquiv K hζ).symm b).2
  map_one' := by
    have hzero : sourceKPAdelicBorelCoordinatesEquiv K hζ (0,1) = 1 := by
      apply Subtype.ext
      change sourceKPAdelicUpperLift K hζ 0 * 1 = 1
      rw [sourceKPAdelicUpperLift_zero, one_mul]
    rw [← hzero, Equiv.symm_apply_apply]
  map_mul' b c := by
    obtain ⟨p, rfl⟩ := (sourceKPAdelicBorelCoordinatesEquiv K hζ).surjective b
    obtain ⟨q, rfl⟩ := (sourceKPAdelicBorelCoordinatesEquiv K hζ).surjective c
    rw [sourceKPAdelicBorelCoordinatesEquiv_mul, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]

def sourceKPAdelicBorelTorusInclusion :
    sourceKPAdelicCoveringTorus K hζ →* sourceKPAdelicCoveringBorel K hζ :=
  Subgroup.inclusion (sourceKPAdelicCoveringTorus_le_borel K hζ)

theorem sourceKPAdelicBorelTorusProjection_coordinates
    (x : 𝔸[K]) (t : sourceKPAdelicCoveringTorus K hζ) :
    sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicBorelCoordinatesEquiv K hζ (x,t)) = t :=
  congrArg Prod.snd ((sourceKPAdelicBorelCoordinatesEquiv K hζ).symm_apply_apply (x,t))

theorem sourceKPAdelicBorelTorusProjection_inclusion (t : sourceKPAdelicCoveringTorus K hζ) :
    sourceKPAdelicBorelTorusProjection K hζ (sourceKPAdelicBorelTorusInclusion K hζ t) = t := by
  have he : sourceKPAdelicBorelCoordinatesEquiv K hζ (0,t) =
      sourceKPAdelicBorelTorusInclusion K hζ t := by
    apply Subtype.ext
    change sourceKPAdelicUpperLift K hζ 0 * t.val = t.val
    rw [sourceKPAdelicUpperLift_zero, one_mul]
  rw [← he, sourceKPAdelicBorelTorusProjection_coordinates]

theorem sourceKPAdelicBorelTorusProjection_surjective :
    Function.Surjective (sourceKPAdelicBorelTorusProjection K hζ) :=
  fun t => ⟨sourceKPAdelicBorelTorusInclusion K hζ t,
    sourceKPAdelicBorelTorusProjection_inclusion K hζ t⟩

theorem sourceKPAdelicCoveringBorel_rational_mem (g : PGL(2, K))
    (hg : g ∈ sourceKPRationalBorel K) :
    sourceKPAdelicProjectiveRationalLift K hζ g ∈ sourceKPAdelicCoveringBorel K hζ := by
  rw [← sourceKPRingBorel_field] at hg
  obtain ⟨x, a, ha⟩ := (sourceKPRingBorel_mem_iff K g).mp hg
  change sourceKPAdelicProjectiveProjection K hζ (sourceKPAdelicProjectiveRationalLift K hζ g) ∈
    sourceKPRingBorel 𝔸[K]
  apply (sourceKPRingBorel_mem_iff 𝔸[K] _).mpr
  refine ⟨algebraMap K 𝔸[K] x, Units.map (algebraMap K 𝔸[K]).toMonoidHom a, ?_⟩
  rw [sourceKPAdelicProjectiveRationalLift_projection, ha, map_mul,
    ProjGenLinGroup.map_mk, sourceKPUpperMatrix_map, sourceKPProjectiveDiagonalHom_map]

def sourceKPAdelicRationalBorelLift :
    sourceKPRationalBorel K →* sourceKPAdelicCoveringBorel K hζ where
  toFun b := ⟨sourceKPAdelicProjectiveRationalLift K hζ b.val,
    sourceKPAdelicCoveringBorel_rational_mem K hζ b.val b.property⟩
  map_one' := Subtype.ext (map_one (sourceKPAdelicProjectiveRationalLift K hζ))
  map_mul' b c := Subtype.ext (map_mul (sourceKPAdelicProjectiveRationalLift K hζ) b.val c.val)

end
end ArtinMatthews
