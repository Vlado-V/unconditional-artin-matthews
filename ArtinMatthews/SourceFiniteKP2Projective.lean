module

public import ArtinMatthews.SourceFiniteKP2Cover
public import ArtinMatthews.SourceKubotaFullScalars


set_option backward.privateInPublic true
@[expose] public section

/-! The local algebraic threefold extension of the actual projective
linear group. It quotients by the proved central ordinary scalar
section. The central cubic kernel survives injectively and exactly. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceFiniteKP2Scalar : (P.adicCompletion K)ˣ →* SourceFiniteKP2Cover K hζ P where
  toFun u := ⟨1, GeneralLinearGroup.scalar (Fin 2) u⟩
  map_one' := by
    apply SourceFiniteKP2Cover.ext
    · rfl
    · exact map_one _
  map_mul' u v := by
    apply SourceFiniteKP2Cover.ext
    · change 1 = 1 * 1 * sourceFiniteKP2Multiplier K hζ P (GeneralLinearGroup.scalar (Fin 2) u)
        (GeneralLinearGroup.scalar (Fin 2) v)
      rw [sourceFiniteKP2Multiplier_scalar_pair, mul_one, mul_one]
    · exact map_mul (GeneralLinearGroup.scalar (Fin 2)) u v

theorem sourceFiniteKP2Scalar_commute (u : (P.adicCompletion K)ˣ) (x : SourceFiniteKP2Cover K hζ P) :
    Commute (sourceFiniteKP2Scalar K hζ P u) x := by
  apply SourceFiniteKP2Cover.ext
  · change 1 * x.central * sourceFiniteKP2Multiplier K hζ P (GeneralLinearGroup.scalar (Fin 2) u) x.base =
      x.central * 1 * sourceFiniteKP2Multiplier K hζ P x.base (GeneralLinearGroup.scalar (Fin 2) u)
    rw [one_mul, mul_one, sourceFiniteKP2Multiplier_scalar_comm]
  · exact GeneralLinearGroup.scalar_commute u x.base

instance sourceFiniteKP2Scalar_normal : (sourceFiniteKP2Scalar K hζ P).range.Normal :=
  Subgroup.normal_of_le_center (by
    rintro _ ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun x => (sourceFiniteKP2Scalar_commute K hζ P u x).eq.symm))

abbrev SourceFiniteKP2Projective :=
  SourceFiniteKP2Cover K hζ P ⧸ (sourceFiniteKP2Scalar K hζ P).range

def sourceFiniteKP2ProjectiveMk : SourceFiniteKP2Cover K hζ P →* SourceFiniteKP2Projective K hζ P :=
  QuotientGroup.mk' _

theorem sourceFiniteKP2ProjectiveMk_scalar (u : (P.adicCompletion K)ˣ) :
    sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Scalar K hζ P u) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

def sourceFiniteKP2ProjectiveProjection :
    SourceFiniteKP2Projective K hζ P →* PGL(2, P.adicCompletion K) :=
  QuotientGroup.lift _ (ProjGenLinGroup.mk.comp (sourceFiniteKP2Projection K hζ P)) (by
    rintro _ ⟨u, rfl⟩
    exact ProjGenLinGroup.mk_scalar u)

theorem sourceFiniteKP2ProjectiveProjection_mk (g : SourceFiniteKP2Cover K hζ P) :
    sourceFiniteKP2ProjectiveProjection K hζ P (sourceFiniteKP2ProjectiveMk K hζ P g) =
      ProjGenLinGroup.mk g.base := rfl

def sourceFiniteKP2ProjectiveCenter :
    rootsOfUnity 3 (P.adicCompletion K) →* SourceFiniteKP2Projective K hζ P :=
  (sourceFiniteKP2ProjectiveMk K hζ P).comp (sourceFiniteKP2Center K hζ P)

theorem sourceFiniteKP2ProjectiveCenter_injective :
    Function.Injective (sourceFiniteKP2ProjectiveCenter K hζ P) := by
  intro z w h
  change sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Center K hζ P z) =
    sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Center K hζ P w) at h
  obtain ⟨s, ⟨u, rfl⟩, hzw⟩ := (QuotientGroup.mk'_eq_mk' _).mp h
  have he := congrArg SourceFiniteKP2Cover.central hzw
  change z * 1 * sourceFiniteKP2Multiplier K hζ P 1 (GeneralLinearGroup.scalar (Fin 2) u) = w at he
  simpa only [sourceFiniteKP2Multiplier_one_left, mul_one] using he

theorem sourceFiniteKP2ProjectiveProjection_surjective :
    Function.Surjective (sourceFiniteKP2ProjectiveProjection K hζ P) := by
  intro p
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective p
  exact ⟨sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Lift K hζ P g), rfl⟩

theorem sourceFiniteKP2Projective_exact :
    (sourceFiniteKP2ProjectiveCenter K hζ P).range = (sourceFiniteKP2ProjectiveProjection K hζ P).ker := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    change ProjGenLinGroup.mk (1 : GL (Fin 2) (P.adicCompletion K)) = 1
    exact ProjGenLinGroup.mk_one
  · intro x
    refine QuotientGroup.induction_on x ?_
    intro g hg
    change ProjGenLinGroup.mk g.base = 1 at hg
    have hbase := ProjGenLinGroup.mk_eq_one.mp hg
    rw [GeneralLinearGroup.center_eq_range_scalar] at hbase
    obtain ⟨u, hu⟩ := hbase
    have hfactor : sourceFiniteKP2Center K hζ P g.central * sourceFiniteKP2Scalar K hζ P u = g := by
      apply SourceFiniteKP2Cover.ext
      · change g.central * 1 * sourceFiniteKP2Multiplier K hζ P 1 (GeneralLinearGroup.scalar (Fin 2) u) = _
        rw [sourceFiniteKP2Multiplier_one_left, mul_one, mul_one]
      · change 1 * GeneralLinearGroup.scalar (Fin 2) u = g.base
        rw [one_mul]
        exact hu
    refine ⟨g.central, ?_⟩
    change sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Center K hζ P g.central) =
      sourceFiniteKP2ProjectiveMk K hζ P g
    calc
      _ = sourceFiniteKP2ProjectiveMk K hζ P
          (sourceFiniteKP2Center K hζ P g.central * sourceFiniteKP2Scalar K hζ P u) := by
        rw [map_mul, sourceFiniteKP2ProjectiveMk_scalar, mul_one]
      _ = _ := congrArg (sourceFiniteKP2ProjectiveMk K hζ P) hfactor

theorem sourceFiniteKP2ProjectiveCenter_commute (z : rootsOfUnity 3 (P.adicCompletion K))
    (x : SourceFiniteKP2Projective K hζ P) : Commute (sourceFiniteKP2ProjectiveCenter K hζ P z) x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range x
  exact (sourceFiniteKP2Center_commute K hζ P z g).map (sourceFiniteKP2ProjectiveMk K hζ P)

def sourceFiniteKP2ProjectiveLift (g : GL (Fin 2) (P.adicCompletion K)) : SourceFiniteKP2Projective K hζ P :=
  sourceFiniteKP2ProjectiveMk K hζ P (sourceFiniteKP2Lift K hζ P g)

theorem sourceFiniteKP2ProjectiveLift_mul (g h : GL (Fin 2) (P.adicCompletion K)) :
    sourceFiniteKP2ProjectiveLift K hζ P g * sourceFiniteKP2ProjectiveLift K hζ P h =
      sourceFiniteKP2ProjectiveCenter K hζ P (sourceFiniteKP2Multiplier K hζ P g h) *
        sourceFiniteKP2ProjectiveLift K hζ P (g * h) := by
  simpa only [sourceFiniteKP2ProjectiveLift, sourceFiniteKP2ProjectiveCenter, MonoidHom.comp_apply, map_mul] using
    congrArg (sourceFiniteKP2ProjectiveMk K hζ P) (sourceFiniteKP2Lift_mul K hζ P g h)

end
end ArtinMatthews
