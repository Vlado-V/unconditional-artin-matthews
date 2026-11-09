module

public import ArtinMatthews.SourceKPFiniteAdeleCover


set_option backward.privateInPublic true
@[expose] public section

/-! The algebraic threefold extension of the actual finite adelic
projective group. The central ordinary scalars are quotiented before
identifying the surviving cubic kernel. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteAdeleScalar : 𝔸ᶠ[K]ˣ →* SourceKPFiniteAdeleCover K hζ where
  toFun u := ⟨1, GeneralLinearGroup.scalar (Fin 2) u⟩
  map_one' := by
    apply SourceKPFiniteAdeleCover.ext
    · rfl
    · exact map_one _
  map_mul' u v := by
    apply SourceKPFiniteAdeleCover.ext
    · change 1 = 1 * 1 * sourceKPAdeleMultiplier K hζ (GeneralLinearGroup.scalar (Fin 2) u)
        (GeneralLinearGroup.scalar (Fin 2) v)
      rw [sourceKPAdeleMultiplier_scalar_pair, mul_one, mul_one]
    · exact map_mul (GeneralLinearGroup.scalar (Fin 2)) u v

theorem sourceKPFiniteAdeleScalar_commute (u : 𝔸ᶠ[K]ˣ) (x : SourceKPFiniteAdeleCover K hζ) :
    Commute (sourceKPFiniteAdeleScalar K hζ u) x := by
  apply SourceKPFiniteAdeleCover.ext
  · change 1 * x.central * sourceKPAdeleMultiplier K hζ (GeneralLinearGroup.scalar (Fin 2) u) x.base =
      x.central * 1 * sourceKPAdeleMultiplier K hζ x.base (GeneralLinearGroup.scalar (Fin 2) u)
    rw [one_mul, mul_one, sourceKPAdeleMultiplier_scalar_comm]
  · exact GeneralLinearGroup.scalar_commute u x.base

instance sourceKPFiniteAdeleScalar_normal : (sourceKPFiniteAdeleScalar K hζ).range.Normal :=
  Subgroup.normal_of_le_center (by
    rintro _ ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun x => (sourceKPFiniteAdeleScalar_commute K hζ u x).eq.symm))

abbrev SourceKPFiniteAdeleProjective :=
  SourceKPFiniteAdeleCover K hζ ⧸ (sourceKPFiniteAdeleScalar K hζ).range

def sourceKPFiniteAdeleProjectiveMk : SourceKPFiniteAdeleCover K hζ →* SourceKPFiniteAdeleProjective K hζ :=
  QuotientGroup.mk' _

theorem sourceKPFiniteAdeleProjectiveMk_scalar (u : 𝔸ᶠ[K]ˣ) :
    sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPFiniteAdeleScalar K hζ u) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

def sourceKPFiniteAdeleProjectiveProjection :
    SourceKPFiniteAdeleProjective K hζ →* PGL(2, 𝔸ᶠ[K]) :=
  QuotientGroup.lift _ (ProjGenLinGroup.mk.comp (sourceKPFiniteAdeleProjection K hζ)) (by
    rintro _ ⟨u, rfl⟩
    exact ProjGenLinGroup.mk_scalar u)

theorem sourceKPFiniteAdeleProjectiveProjection_mk (g : SourceKPFiniteAdeleCover K hζ) :
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteAdeleProjectiveMk K hζ g) =
      ProjGenLinGroup.mk g.base := rfl

def sourceKPFiniteAdeleProjectiveCenter :
    rootsOfUnity 3 K →* SourceKPFiniteAdeleProjective K hζ :=
  (sourceKPFiniteAdeleProjectiveMk K hζ).comp (sourceKPFiniteAdeleCenter K hζ)

theorem sourceKPFiniteAdeleProjectiveCenter_injective :
    Function.Injective (sourceKPFiniteAdeleProjectiveCenter K hζ) := by
  intro z w h
  change sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPFiniteAdeleCenter K hζ z) =
    sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPFiniteAdeleCenter K hζ w) at h
  obtain ⟨s, ⟨u, rfl⟩, hzw⟩ := (QuotientGroup.mk'_eq_mk' _).mp h
  have he := congrArg SourceKPFiniteAdeleCover.central hzw
  change z * 1 * sourceKPAdeleMultiplier K hζ 1 (GeneralLinearGroup.scalar (Fin 2) u) = w at he
  simpa only [sourceKPAdeleMultiplier_one_left, mul_one] using he

theorem sourceKPFiniteAdeleProjectiveProjection_surjective :
    Function.Surjective (sourceKPFiniteAdeleProjectiveProjection K hζ) := by
  intro p
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective p
  exact ⟨sourceKPFiniteAdeleProjectiveMk K hζ ⟨1, g⟩, rfl⟩

theorem sourceKPFiniteAdeleProjective_exact :
    (sourceKPFiniteAdeleProjectiveCenter K hζ).range = (sourceKPFiniteAdeleProjectiveProjection K hζ).ker := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    change ProjGenLinGroup.mk (1 : GL (Fin 2) 𝔸ᶠ[K]) = 1
    exact ProjGenLinGroup.mk_one
  · intro x
    refine QuotientGroup.induction_on x ?_
    intro g hg
    change ProjGenLinGroup.mk g.base = 1 at hg
    have hbase := ProjGenLinGroup.mk_eq_one.mp hg
    rw [GeneralLinearGroup.center_eq_range_scalar] at hbase
    obtain ⟨u, hu⟩ := hbase
    have hfactor : sourceKPFiniteAdeleCenter K hζ g.central * sourceKPFiniteAdeleScalar K hζ u = g := by
      apply SourceKPFiniteAdeleCover.ext
      · change g.central * 1 * sourceKPAdeleMultiplier K hζ 1 (GeneralLinearGroup.scalar (Fin 2) u) = _
        rw [sourceKPAdeleMultiplier_one_left, mul_one, mul_one]
      · change 1 * GeneralLinearGroup.scalar (Fin 2) u = g.base
        rw [one_mul]
        exact hu
    refine ⟨g.central, ?_⟩
    change sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPFiniteAdeleCenter K hζ g.central) =
      sourceKPFiniteAdeleProjectiveMk K hζ g
    calc
      _ = sourceKPFiniteAdeleProjectiveMk K hζ
          (sourceKPFiniteAdeleCenter K hζ g.central * sourceKPFiniteAdeleScalar K hζ u) := by
        rw [map_mul, sourceKPFiniteAdeleProjectiveMk_scalar, mul_one]
      _ = _ := congrArg (sourceKPFiniteAdeleProjectiveMk K hζ) hfactor

theorem sourceKPFiniteAdeleProjectiveCenter_commute (z : rootsOfUnity 3 K)
    (x : SourceKPFiniteAdeleProjective K hζ) : Commute (sourceKPFiniteAdeleProjectiveCenter K hζ z) x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (sourceKPFiniteAdeleScalar K hζ).range x
  exact (sourceKPFiniteAdeleCenter_commute K hζ z g).map (sourceKPFiniteAdeleProjectiveMk K hζ)

end
end ArtinMatthews
