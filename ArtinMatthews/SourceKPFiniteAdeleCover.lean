module

public import ArtinMatthews.SourceKPAdeleMultiplier


set_option backward.privateInPublic true
@[expose] public section

/-! The algebraic threefold extension of the actual finite adelic
general linear group, built from the proved finite product multiplier. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

structure SourceKPFiniteAdeleCover (K : Type) [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) where
  central : rootsOfUnity 3 K
  base : GL (Fin 2) 𝔸ᶠ[K]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

@[ext] theorem SourceKPFiniteAdeleCover.ext {x y : SourceKPFiniteAdeleCover K hζ}
    (hc : x.central = y.central) (hb : x.base = y.base) : x = y := by
  cases x
  cases y
  congr

instance sourceKPFiniteAdeleCoverGroup : Group (SourceKPFiniteAdeleCover K hζ) where
  mul x y := ⟨x.central * y.central * sourceKPAdeleMultiplier K hζ x.base y.base, x.base * y.base⟩
  one := ⟨1, 1⟩
  inv x := ⟨(x.central * sourceKPAdeleMultiplier K hζ x.base⁻¹ x.base)⁻¹, x.base⁻¹⟩
  mul_assoc x y z := by
    apply SourceKPFiniteAdeleCover.ext
    · change (x.central * y.central * sourceKPAdeleMultiplier K hζ x.base y.base) * z.central *
          sourceKPAdeleMultiplier K hζ (x.base * y.base) z.base =
        x.central * (y.central * z.central * sourceKPAdeleMultiplier K hζ y.base z.base) *
          sourceKPAdeleMultiplier K hζ x.base (y.base * z.base)
      calc
        _ = (x.central * y.central * z.central) *
            (sourceKPAdeleMultiplier K hζ x.base y.base * sourceKPAdeleMultiplier K hζ (x.base * y.base) z.base) :=
          by ac_rfl
        _ = _ := by rw [sourceKPAdeleMultiplier_cocycle]; ac_rfl
    · exact mul_assoc x.base y.base z.base
  one_mul x := by
    apply SourceKPFiniteAdeleCover.ext
    · change 1 * x.central * sourceKPAdeleMultiplier K hζ 1 x.base = x.central
      rw [one_mul, sourceKPAdeleMultiplier_one_left, mul_one]
    · exact one_mul x.base
  mul_one x := by
    apply SourceKPFiniteAdeleCover.ext
    · change x.central * 1 * sourceKPAdeleMultiplier K hζ x.base 1 = x.central
      rw [mul_one, sourceKPAdeleMultiplier_one_right, mul_one]
    · exact mul_one x.base
  inv_mul_cancel x := by
    apply SourceKPFiniteAdeleCover.ext
    · change (x.central * sourceKPAdeleMultiplier K hζ x.base⁻¹ x.base)⁻¹ * x.central *
          sourceKPAdeleMultiplier K hζ x.base⁻¹ x.base = 1
      rw [mul_assoc, inv_mul_cancel]
    · exact inv_mul_cancel x.base

def sourceKPFiniteAdeleProjection : SourceKPFiniteAdeleCover K hζ →* GL (Fin 2) 𝔸ᶠ[K] where
  toFun := SourceKPFiniteAdeleCover.base
  map_one' := rfl
  map_mul' _ _ := rfl

def sourceKPFiniteAdeleCenter : rootsOfUnity 3 K →* SourceKPFiniteAdeleCover K hζ where
  toFun z := ⟨z, 1⟩
  map_one' := rfl
  map_mul' z w := by
    apply SourceKPFiniteAdeleCover.ext
    · change z * w = z * w * sourceKPAdeleMultiplier K hζ 1 1
      rw [sourceKPAdeleMultiplier_one_left, mul_one]
    · exact (one_mul _).symm

theorem sourceKPFiniteAdeleCenter_injective : Function.Injective (sourceKPFiniteAdeleCenter K hζ) :=
  fun _ _ he => congrArg SourceKPFiniteAdeleCover.central he

theorem sourceKPFiniteAdeleProjection_surjective :
    Function.Surjective (sourceKPFiniteAdeleProjection K hζ) :=
  fun g => ⟨⟨1, g⟩, rfl⟩

theorem sourceKPFiniteAdeleCover_exact :
    (sourceKPFiniteAdeleCenter K hζ).range = (sourceKPFiniteAdeleProjection K hζ).ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hx
    change x.base = 1 at hx
    exact ⟨x.central, SourceKPFiniteAdeleCover.ext K hζ rfl hx.symm⟩

theorem sourceKPFiniteAdeleCenter_commute (z : rootsOfUnity 3 K) (x : SourceKPFiniteAdeleCover K hζ) :
    Commute (sourceKPFiniteAdeleCenter K hζ z) x := by
  apply SourceKPFiniteAdeleCover.ext
  · change z * x.central * sourceKPAdeleMultiplier K hζ 1 x.base =
      x.central * z * sourceKPAdeleMultiplier K hζ x.base 1
    rw [sourceKPAdeleMultiplier_one_left, sourceKPAdeleMultiplier_one_right, mul_one, mul_one, mul_comm]
  · change 1 * x.base = x.base * 1
    rw [one_mul, mul_one]

end
end ArtinMatthews
