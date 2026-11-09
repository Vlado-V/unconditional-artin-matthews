module

public import ArtinMatthews.SourceKPArchGramProduct
public import ArtinMatthews.SourceKPArchCompactOrbifold


set_option backward.privateInPublic true
@[expose] public section

/-! The actual archimedean scalar-unitary quotient is a product of upper half-spaces. -/
namespace ArtinMatthews
open NumberField Matrix Matrix.GeneralLinearGroup SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchBaseCompactSubgroup_mem_iff (q : PGL(2, InfiniteAdeleRing K)) :
    q ∈ sourceKPArchBaseCompactSubgroup K hζ ↔
      ∃ k : InfinitePlace K → Matrix.unitaryGroup (Fin 2) ℂ,
        q = ProjGenLinGroup.mk (sourceKPArchUnitaryMatrix K hζ k) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    choose k hk using ha.2
    refine ⟨k, ?_⟩
    change ProjGenLinGroup.mk (GeneralLinearGroup.map (RingHom.fst _ _) a) = _
    congr 1
    apply (sourceArchGLPiEquiv K).injective
    funext v
    apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
    rw [sourceKPArchUnitaryMatrix_at]
    exact (hk v).symm
  · rintro ⟨k, rfl⟩
    let p : (InfinitePlace K → Matrix.unitaryGroup (Fin 2) ℂ) ×
        sourceKPFiniteIntegralMatrixGroup K := (k, 1)
    refine ⟨sourceKPAdelicBaseCompactParam K hζ p, ?_, ?_⟩
    · rw [← sourceKPAdelicBaseCompactParam_range K hζ]
      exact Set.mem_range_self p
    · change ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K
        (sourceKPAdelicBaseCompactParam K hζ p)).1) = _
      rw [sourceKPAdelicBaseCompactParam, MulEquiv.apply_symm_apply]
      rfl

def sourceKPArchGramCoordinates (q : PGL(2, InfiniteAdeleRing K)) :
    SourceKPArchUpperHalfSpace K :=
  Quotient.liftOn q (sourceKPArchGramCoordinatesMatrix K hζ) (by
    intro a b hab
    have he : ProjGenLinGroup.mk a = ProjGenLinGroup.mk b := Quotient.sound hab
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    rw [← hu, sourceKPArchGramCoordinatesMatrix_scalar])

theorem sourceKPArchGramCoordinates_mk (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchGramCoordinates K hζ (ProjGenLinGroup.mk g) =
      sourceKPArchGramCoordinatesMatrix K hζ g := rfl

theorem sourceKPArchGramCoordinates_continuous :
    Continuous (sourceKPArchGramCoordinates K hζ) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact sourceKPArchGramCoordinatesMatrix_continuous K hζ

theorem sourceKPArchGramCoordinates_compact (q k : PGL(2, InfiniteAdeleRing K))
    (hk : k ∈ sourceKPArchBaseCompactSubgroup K hζ) :
    sourceKPArchGramCoordinates K hζ (q*k) = sourceKPArchGramCoordinates K hζ q := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective q
  obtain ⟨u, rfl⟩ := (sourceKPArchBaseCompactSubgroup_mem_iff K hζ k).mp hk
  rw [← map_mul, sourceKPArchGramCoordinates_mk, sourceKPArchGramCoordinates_mk]
  exact sourceKPArchGramCoordinatesMatrix_unitary K hζ g u

def sourceKPArchSymmetricCoordinates (q : SourceKPArchSymmetricSpace K hζ) :
    SourceKPArchUpperHalfSpace K :=
  Quotient.liftOn' q (sourceKPArchGramCoordinates K hζ) (by
    intro a b hab
    have hmem := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * (a⁻¹*b) := by group
    rw [hb, sourceKPArchGramCoordinates_compact K hζ a _ hmem])

theorem sourceKPArchSymmetricCoordinates_mk (q : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchSymmetricCoordinates K hζ (QuotientGroup.mk q) =
      sourceKPArchGramCoordinates K hζ q := rfl

theorem sourceKPArchSymmetricCoordinates_continuous :
    Continuous (sourceKPArchSymmetricCoordinates K hζ) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact sourceKPArchGramCoordinates_continuous K hζ

def sourceKPArchSymmetricSection (p : SourceKPArchUpperHalfSpace K) :
    SourceKPArchSymmetricSpace K hζ :=
  QuotientGroup.mk (ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ p))

theorem sourceKPArchSymmetricSection_continuous :
    Continuous (sourceKPArchSymmetricSection K hζ) :=
  continuous_quotient_mk'.comp
    (continuous_quotient_mk'.comp (sourceKPArchUpperHalfSection_continuous K hζ))

theorem sourceKPArchSymmetricCoordinates_section (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchSymmetricCoordinates K hζ (sourceKPArchSymmetricSection K hζ p) = p :=
  sourceKPArchGramCoordinatesMatrix_section K hζ p

theorem sourceKPArchSymmetricSection_coordinates (q : SourceKPArchSymmetricSpace K hζ) :
    sourceKPArchSymmetricSection K hζ (sourceKPArchSymmetricCoordinates K hζ q) = q := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective q
  obtain ⟨u, k, hg⟩ := sourceKPArchGramMatrix_normal_form K hζ g
  change QuotientGroup.mk (ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ
    (sourceKPArchGramCoordinatesMatrix K hζ g))) = QuotientGroup.mk (ProjGenLinGroup.mk g)
  have hm : ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ
        (sourceKPArchGramCoordinatesMatrix K hζ g)) *
        ProjGenLinGroup.mk (sourceKPArchUnitaryMatrix K hζ k) := by
    conv_lhs => rw [hg]
    rw [map_mul, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  rw [hm, QuotientGroup.mk_mul_of_mem]
  exact (sourceKPArchBaseCompactSubgroup_mem_iff K hζ _).mpr ⟨k, rfl⟩

def sourceKPArchSymmetricHomeomorph :
    SourceKPArchSymmetricSpace K hζ ≃ₜ SourceKPArchUpperHalfSpace K where
  toFun := sourceKPArchSymmetricCoordinates K hζ
  invFun := sourceKPArchSymmetricSection K hζ
  left_inv := sourceKPArchSymmetricSection_coordinates K hζ
  right_inv := sourceKPArchSymmetricCoordinates_section K hζ
  continuous_toFun := sourceKPArchSymmetricCoordinates_continuous K hζ
  continuous_invFun := sourceKPArchSymmetricSection_continuous K hζ

theorem sourceKPArchGramCoordinates_fiber (q r : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchGramCoordinates K hζ q = sourceKPArchGramCoordinates K hζ r ↔
      (QuotientGroup.mk q : SourceKPArchSymmetricSpace K hζ) = QuotientGroup.mk r := by
  constructor
  · intro h
    exact (sourceKPArchSymmetricHomeomorph K hζ).injective h
  · intro h
    exact congrArg (sourceKPArchSymmetricCoordinates K hζ) h

theorem sourceKPArchGramCoordinates_eq_iff (q r : PGL(2, InfiniteAdeleRing K)) :
    sourceKPArchGramCoordinates K hζ q = sourceKPArchGramCoordinates K hζ r ↔
      q⁻¹ * r ∈ sourceKPArchBaseCompactSubgroup K hζ := by
  rw [sourceKPArchGramCoordinates_fiber, QuotientGroup.eq]

theorem sourceKPArchGramCoordinatesMatrix_fiber
    (g h : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceKPArchGramCoordinatesMatrix K hζ g = sourceKPArchGramCoordinatesMatrix K hζ h ↔
      (ProjGenLinGroup.mk g)⁻¹ * ProjGenLinGroup.mk h ∈ sourceKPArchBaseCompactSubgroup K hζ :=
  sourceKPArchGramCoordinates_eq_iff K hζ (ProjGenLinGroup.mk g) (ProjGenLinGroup.mk h)

end
end ArtinMatthews
