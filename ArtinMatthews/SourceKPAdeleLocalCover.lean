module

public import ArtinMatthews.SourceKPAdeleSingleMatrix
public import ArtinMatthews.SourceKPAdelicProjective
import ArtinMatthews.SourceAdelicIwasawaAssembly


set_option backward.privateInPublic true
@[expose] public section

/-! The actual local cubic cover maps to the finite adelic cover with
the inverse compact-section cochain. Covers at distinct places commute
after this exact phase correction. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPAdeleMultiplier_single (g h : GL (Fin 2) (P.adicCompletion K)) :
    sourceKPAdeleMultiplier K hζ (sourceKPAdeleSingleMatrix K P g) (sourceKPAdeleSingleMatrix K P h) =
      (sourceKPRootsTransport K hζ P).symm (sourceKPFiniteTwistedMultiplier K hζ P g h) := by
  rw [sourceKPAdeleMultiplier, finprod_eq_single _ P]
  · rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleSingleMatrix_same, sourceKPAdeleSingleMatrix_same]
  · intro Q hQP
    rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleSingleMatrix_other K P Q hQP,
      sourceKPFiniteTwistedMultiplier_one_left, map_one]

theorem sourceKPAdeleMultiplier_disjoint (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (g : GL (Fin 2) (P.adicCompletion K)) (h : GL (Fin 2) (Q.adicCompletion K)) :
    sourceKPAdeleMultiplier K hζ (sourceKPAdeleSingleMatrix K P g) (sourceKPAdeleSingleMatrix K Q h) = 1 := by
  rw [sourceKPAdeleMultiplier, ← finprod_one (α := HeightOneSpectrum (𝓞 K))]
  apply finprod_congr
  intro R
  by_cases hRP : R = P
  · subst R
    rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleSingleMatrix_other K Q P hQP.symm,
      sourceKPFiniteTwistedMultiplier_one_right, map_one]
  · rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleSingleMatrix_other K P R hRP,
      sourceKPFiniteTwistedMultiplier_one_left, map_one]

def sourceKPAdeleLocalCover : SourceFiniteKP2Cover K hζ P →* SourceKPFiniteAdeleCover K hζ where
  toFun g :=
    ⟨(sourceKPRootsTransport K hζ P).symm (g.central / sourceKPFinitePhase K hζ P g.base),
      sourceKPAdeleSingleMatrix K P g.base⟩
  map_one' := by
    apply SourceKPFiniteAdeleCover.ext
    · change (sourceKPRootsTransport K hζ P).symm (1 / sourceKPFinitePhase K hζ P 1) = 1
      rw [sourceKPFinitePhase_one, div_one, map_one]
    · exact (sourceKPAdeleSingleMatrix K P).map_one
  map_mul' g h := by
    apply SourceKPFiniteAdeleCover.ext
    · change (sourceKPRootsTransport K hζ P).symm
        (g.central * h.central * sourceFiniteKP2Multiplier K hζ P g.base h.base /
          sourceKPFinitePhase K hζ P (g.base * h.base)) =
        (sourceKPRootsTransport K hζ P).symm (g.central / sourceKPFinitePhase K hζ P g.base) *
          (sourceKPRootsTransport K hζ P).symm (h.central / sourceKPFinitePhase K hζ P h.base) *
          sourceKPAdeleMultiplier K hζ (sourceKPAdeleSingleMatrix K P g.base) (sourceKPAdeleSingleMatrix K P h.base)
      rw [sourceKPAdeleMultiplier_single, ← map_mul, ← map_mul]
      apply congrArg (sourceKPRootsTransport K hζ P).symm
      unfold sourceKPFiniteTwistedMultiplier sourceKPCochainTwist
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div]
      abel
    · exact (sourceKPAdeleSingleMatrix K P).map_mul g.base h.base

theorem sourceKPAdeleLocalCover_commute (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (g : SourceFiniteKP2Cover K hζ P) (h : SourceFiniteKP2Cover K hζ Q) :
    Commute (sourceKPAdeleLocalCover K hζ P g) (sourceKPAdeleLocalCover K hζ Q h) := by
  apply SourceKPFiniteAdeleCover.ext
  · change _ * _ * sourceKPAdeleMultiplier K hζ (sourceKPAdeleSingleMatrix K P g.base) (sourceKPAdeleSingleMatrix K Q h.base) =
      _ * _ * sourceKPAdeleMultiplier K hζ (sourceKPAdeleSingleMatrix K Q h.base) (sourceKPAdeleSingleMatrix K P g.base)
    rw [sourceKPAdeleMultiplier_disjoint K hζ P Q hQP,
      sourceKPAdeleMultiplier_disjoint K hζ Q P hQP.symm, mul_one, mul_one, mul_comm]
  · exact sourceKPAdeleSingleMatrix_commute K P Q hQP g.base h.base

def sourceKPAdeleLocalUnit (u : (P.adicCompletion K)ˣ) : 𝔸ᶠ[K]ˣ :=
  sourceKPIdeleFiniteUnit K (IdeleGroup.ofAdicCompletion (𝓞 K) K P u)

theorem sourceKPAdeleLocalUnit_same (u : (P.adicCompletion K)ˣ) :
    Units.map (sourceKPAdeleEval K P).toMonoidHom (sourceKPAdeleLocalUnit K P u) = u := by
  apply Units.ext
  change Pi.mulSingle (M := fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletion K) P
    (u : P.adicCompletion K) P = (u : P.adicCompletion K)
  exact Pi.mulSingle_eq_same P _

theorem sourceKPAdeleLocalUnit_other (u : (P.adicCompletion K)ˣ) (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P) :
    Units.map (sourceKPAdeleEval K Q).toMonoidHom (sourceKPAdeleLocalUnit K P u) = 1 := by
  apply Units.ext
  change Pi.mulSingle (M := fun R : HeightOneSpectrum (𝓞 K) => R.adicCompletion K) P
    (u : P.adicCompletion K) Q = 1
  exact Pi.mulSingle_eq_of_ne hQP _

theorem sourceKPAdeleLocalCover_scalar (u : (P.adicCompletion K)ˣ) :
    sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2Scalar K hζ P u) =
      sourceKPFiniteAdeleScalar K hζ (sourceKPAdeleLocalUnit K P u) := by
  apply SourceKPFiniteAdeleCover.ext
  · change (sourceKPRootsTransport K hζ P).symm (1 / sourceKPFinitePhase K hζ P (GeneralLinearGroup.scalar (Fin 2) u)) = 1
    rw [sourceKPFinitePhase_scalar, div_one, map_one]
  · apply sourceKPAdeleMatrixAt_ext K
    intro Q
    change sourceKPAdeleMatrixAt K Q (sourceKPAdeleSingleMatrix K P (GeneralLinearGroup.scalar (Fin 2) u)) =
      sourceKPAdeleMatrixAt K Q (GeneralLinearGroup.scalar (Fin 2) (sourceKPAdeleLocalUnit K P u))
    rw [sourceKPAdeleMatrixAt_scalar]
    by_cases hQP : Q = P
    · subst Q
      rw [sourceKPAdeleSingleMatrix_same, sourceKPAdeleLocalUnit_same]
    · rw [sourceKPAdeleSingleMatrix_other K P Q hQP, sourceKPAdeleLocalUnit_other K P u Q hQP, map_one]

def sourceKPAdeleLocalProjective : SourceFiniteKP2Projective K hζ P →* SourceKPFiniteAdeleProjective K hζ :=
  QuotientGroup.lift _ ((sourceKPFiniteAdeleProjectiveMk K hζ).comp (sourceKPAdeleLocalCover K hζ P)) (by
    rintro _ ⟨u, rfl⟩
    change sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPAdeleLocalCover K hζ P (sourceFiniteKP2Scalar K hζ P u)) = 1
    rw [sourceKPAdeleLocalCover_scalar, sourceKPFiniteAdeleProjectiveMk_scalar])

theorem sourceKPAdeleLocalProjective_mk (g : SourceFiniteKP2Cover K hζ P) :
    sourceKPAdeleLocalProjective K hζ P (sourceFiniteKP2ProjectiveMk K hζ P g) =
      sourceKPFiniteAdeleProjectiveMk K hζ (sourceKPAdeleLocalCover K hζ P g) := rfl

def sourceKPAdelicLocalProjective : SourceFiniteKP2Projective K hζ P →* SourceKPAdelicProjective K hζ :=
  (1 : SourceFiniteKP2Projective K hζ P →* PGL(2, InfiniteAdeleRing K)).prod (sourceKPAdeleLocalProjective K hζ P)

theorem sourceKPAdelicLocalProjective_commute (Q : HeightOneSpectrum (𝓞 K)) (hQP : Q ≠ P)
    (g : SourceFiniteKP2Projective K hζ P) (h : SourceFiniteKP2Projective K hζ Q) :
    Commute (sourceKPAdelicLocalProjective K hζ P g) (sourceKPAdelicLocalProjective K hζ Q h) := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ Q).range h
  apply Prod.ext
  · rfl
  · exact congrArg (sourceKPFiniteAdeleProjectiveMk K hζ) (sourceKPAdeleLocalCover_commute K hζ P Q hQP g' h').eq

end
end ArtinMatthews
