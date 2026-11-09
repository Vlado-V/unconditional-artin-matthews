module

public import ArtinMatthews.SourceKPAdelicBorel
public import ArtinMatthews.SourceAdelicScalarHaar
public import Mathlib.Algebra.Ring.AddAut


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rational Borel scales the canonical upper-root splitting
by its normalized diagonal entry. -/
namespace ArtinMatthews
open NumberField Matrix IsDedekindDomain MeasureTheory
open scoped NumberField MatrixGroups AdeleRing

noncomputable section

variable (K : Type) [Field K]

def sourceKPRationalCuspCoordinates : K × Kˣ ≃ sourceKPRationalBorel K :=
  Equiv.ofBijective
    (fun p => ⟨ProjGenLinGroup.mk (sourceKPUpperMatrix K p.1) * sourceKPProjectiveDiagonalHom K p.2,
      sourceKPRingBorel_field (F := K) ▸ (sourceKPRingBorel_mem_iff K _).mpr ⟨p.1, p.2, rfl⟩⟩)
    ⟨fun _ _ h => sourceKPRingBorel_coordinates_injective K (congrArg Subtype.val h), by
      intro g
      have hg : g.val ∈ sourceKPRingBorel K := by
        rw [sourceKPRingBorel_field]
        exact g.property
      obtain ⟨x, a, h⟩ := (sourceKPRingBorel_mem_iff K _).mp hg
      exact ⟨(x,a), Subtype.ext h.symm⟩⟩

theorem sourceKPRationalCuspCoordinates_val (x : K) (a : Kˣ) :
    (sourceKPRationalCuspCoordinates K (x,a)).val =
      ProjGenLinGroup.mk (sourceKPUpperMatrix K x) * sourceKPProjectiveDiagonalHom K a := rfl

theorem sourceKPRationalCuspCoordinates_mul (p q : K × Kˣ) :
    sourceKPRationalCuspCoordinates K p * sourceKPRationalCuspCoordinates K q =
      sourceKPRationalCuspCoordinates K (p.1 + (p.2 : K) * q.1, p.2 * q.2) := by
  apply Subtype.ext
  change (ProjGenLinGroup.mk (sourceKPUpperMatrix K p.1) *
      ProjGenLinGroup.mk (sourceKPDiagonalHom K p.2)) *
    (ProjGenLinGroup.mk (sourceKPUpperMatrix K q.1) *
      ProjGenLinGroup.mk (sourceKPDiagonalHom K q.2)) =
    ProjGenLinGroup.mk (sourceKPUpperMatrix K (p.1 + (p.2 : K) * q.1)) *
      ProjGenLinGroup.mk (sourceKPDiagonalHom K (p.2*q.2))
  simp only [← map_mul]
  apply congrArg ProjGenLinGroup.mk
  calc
    _ = sourceKPUpperMatrix K p.1 *
        (sourceKPDiagonalHom K p.2 * sourceKPUpperMatrix K q.1) *
        sourceKPDiagonalHom K q.2 := by simp only [mul_assoc]
    _ = _ := by
      rw [sourceKPDiagonalHom_upper, sourceKPUpperMatrix_add, map_mul]
      simp only [mul_assoc]

def sourceKPRationalCuspScale : sourceKPRationalBorel K →* Kˣ where
  toFun g := ((sourceKPRationalCuspCoordinates K).symm g).2
  map_one' := by
    have he : sourceKPRationalCuspCoordinates K (0,1) = 1 := by
      apply Subtype.ext
      rw [sourceKPRationalCuspCoordinates_val, sourceKPUpperMatrix_zero, map_one, map_one, one_mul]
      rfl
    rw [← he, Equiv.symm_apply_apply]
  map_mul' g h := by
    obtain ⟨p,rfl⟩ := (sourceKPRationalCuspCoordinates K).surjective g
    obtain ⟨q,rfl⟩ := (sourceKPRationalCuspCoordinates K).surjective h
    rw [sourceKPRationalCuspCoordinates_mul, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[simp] theorem sourceKPRationalCuspScale_coordinates (p : K × Kˣ) :
    sourceKPRationalCuspScale K (sourceKPRationalCuspCoordinates K p) = p.2 :=
  congrArg Prod.snd ((sourceKPRationalCuspCoordinates K).symm_apply_apply p)

def sourceKPRationalCuspUpper : Multiplicative K →* sourceKPRationalBorel K where
  toFun x := sourceKPRationalCuspCoordinates K (x.toAdd, 1)
  map_one' := by
    apply Subtype.ext
    rw [sourceKPRationalCuspCoordinates_val, show (1 : Multiplicative K).toAdd = 0 from rfl,
      sourceKPUpperMatrix_zero, map_one, map_one, one_mul]
    rfl
  map_mul' x y := by
    rw [sourceKPRationalCuspCoordinates_mul]
    congr 1
    change (x.toAdd + y.toAdd, (1 : Kˣ)) = (x.toAdd + (1 : K) * y.toAdd, 1 * 1)
    simp

theorem sourceKPRationalCuspUpper_val (x : Multiplicative K) :
    (sourceKPRationalCuspUpper K x).val = sourcePGL2Upper x.toAdd := by
  change (sourceKPRationalCuspCoordinates K (x.toAdd,1)).val = _
  rw [sourceKPRationalCuspCoordinates_val, map_one, mul_one, sourceKPUpperMatrix_field]

@[simp] theorem sourceKPRationalCuspScale_upper (x : Multiplicative K) :
    sourceKPRationalCuspScale K (sourceKPRationalCuspUpper K x) = 1 :=
  sourceKPRationalCuspScale_coordinates K (x.toAdd,1)

def sourceKPCuspUnitAddAut (R : Type*) [Ring R] :
    Rˣ →* MulAut (Multiplicative R) :=
  (MulAutMultiplicative R).symm.toMonoidHom.comp AddAut.mulLeft

theorem sourceKPCuspUnitAddAut_apply (R : Type*) [Ring R] (a : Rˣ) (x : Multiplicative R) :
    (sourceKPCuspUnitAddAut R a x).toAdd = (a : R) * x.toAdd := rfl

variable [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPCuspRationalScaleAut : sourceKPRationalBorel K →* MulAut (Multiplicative K) :=
  (sourceKPCuspUnitAddAut K).comp (sourceKPRationalCuspScale K)

def sourceKPCuspAdelicScaleAut : sourceKPRationalBorel K →* MulAut (Multiplicative 𝔸[K]) :=
  (sourceKPCuspUnitAddAut 𝔸[K]).comp
    ((Units.map (algebraMap K 𝔸[K]).toMonoidHom).comp (sourceKPRationalCuspScale K))

def sourceKPCuspRationalAddHom : Multiplicative K →* Multiplicative 𝔸[K] :=
  (algebraMap K 𝔸[K]).toAddMonoidHom.toMultiplicative

theorem sourceKPCuspAdelicScaleAut_apply (b : sourceKPRationalBorel K) (x : Multiplicative 𝔸[K]) :
    (sourceKPCuspAdelicScaleAut K b x).toAdd =
      algebraMap K 𝔸[K] (sourceKPRationalCuspScale K b : K) * x.toAdd := rfl

theorem sourceKPCuspRationalAddHom_scale (b : sourceKPRationalBorel K) (x : Multiplicative K) :
    sourceKPCuspRationalAddHom K (sourceKPCuspRationalScaleAut K b x) =
      sourceKPCuspAdelicScaleAut K b (sourceKPCuspRationalAddHom K x) :=
  map_mul (algebraMap K 𝔸[K]) _ _

theorem sourceKPCuspAdelicScaleAut_upper (x : Multiplicative K) :
    sourceKPCuspAdelicScaleAut K (sourceKPRationalCuspUpper K x) = 1 := by
  simp [sourceKPCuspAdelicScaleAut]

theorem sourceKPRationalCuspUpper_lift (x : Multiplicative K) :
    sourceKPAdelicProjectiveRationalLift K hζ (sourceKPRationalCuspUpper K x).val =
      sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] x.toAdd) := by
  rw [sourceKPRationalCuspUpper_val, sourceKPAdelicUpperLift_rational]

theorem sourceKPRationalCuspScale_upper_covariance (b : sourceKPRationalBorel K) (x : 𝔸[K]) :
    sourceKPAdelicProjectiveRationalLift K hζ b.val * sourceKPAdelicUpperLift K hζ x =
      sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] (sourceKPRationalCuspScale K b : K) * x) *
        sourceKPAdelicProjectiveRationalLift K hζ b.val := by
  obtain ⟨⟨z,a⟩,rfl⟩ := (sourceKPRationalCuspCoordinates K).surjective b
  rw [sourceKPRationalCuspScale_coordinates, sourceKPRationalCuspCoordinates_val, map_mul]
  let t := sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K a)
  let u := algebraMap K 𝔸[K] z
  have hupper : sourceKPAdelicProjectiveRationalLift K hζ
      (ProjGenLinGroup.mk (sourceKPUpperMatrix K z)) = sourceKPAdelicUpperLift K hζ u := by
    rw [sourceKPUpperMatrix_field]
    exact (sourceKPAdelicUpperLift_rational K hζ z).symm
  rw [hupper]
  change (sourceKPAdelicUpperLift K hζ u * t) * sourceKPAdelicUpperLift K hζ x =
    sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] (a : K) * x) *
      (sourceKPAdelicUpperLift K hζ u * t)
  have ht : sourceKPAdelicProjectiveProjection K hζ t =
      sourceKPProjectiveDiagonalHom 𝔸[K] (IdeleGroup.unitEmbedding (𝓞 K) K a) := by
    dsimp only [t]
    rw [sourceKPAdelicProjectiveRationalLift_projection, sourceKPProjectiveDiagonalHom_map]
    rfl
  rw [mul_assoc, sourceKPAdelicTorus_upper_of_projection K hζ t _ ht]
  change sourceKPAdelicUpperLift K hζ u *
      (sourceKPAdelicUpperLift K hζ (algebraMap K 𝔸[K] (a : K) * x) * t) = _
  rw [← mul_assoc, ← sourceKPAdelicUpperLift_add, add_comm u, sourceKPAdelicUpperLift_add, mul_assoc]

end
end ArtinMatthews
