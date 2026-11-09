module

public import ArtinMatthews.SourceCubicTorusCocycle


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine central extension of the actual S-local torus by μ3.
Its law is constructed from the proved source Hilbert cocycle. The
ordinary section on the actual chosen B and Weyl inversion are derived,
without assuming a PGL2 cover or an automorphic theta representation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section

structure SourceCubicTorus (K : Type) [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S : Finset (HeightOneSpectrum (𝓞 K))) where
  central : rootsOfUnity 3 K
  base : SourceCubicTorusBase K S

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

@[ext] theorem SourceCubicTorus.ext
    {x y : SourceCubicTorus K hζ S} (hc : x.central = y.central) (hb : x.base = y.base) : x = y := by
  cases x
  cases y
  congr

instance sourceCubicTorusGroup : Group (SourceCubicTorus K hζ S) where
  mul x y := ⟨x.central * y.central * sourceCubicTorusPair K hζ S x.base y.base, x.base * y.base⟩
  one := ⟨1, 1⟩
  inv x := ⟨x.central⁻¹, x.base⁻¹⟩
  mul_assoc x y z := by
    apply SourceCubicTorus.ext
    · change (x.central * y.central * sourceCubicTorusPair K hζ S x.base y.base) * z.central *
        sourceCubicTorusPair K hζ S (x.base * y.base) z.base =
        x.central * (y.central * z.central * sourceCubicTorusPair K hζ S y.base z.base) *
          sourceCubicTorusPair K hζ S x.base (y.base * z.base)
      have h := sourceCubicTorusPair_cocycle K hζ S x.base y.base z.base
      calc
        _ = (x.central * y.central * z.central) *
            (sourceCubicTorusPair K hζ S x.base y.base *
              sourceCubicTorusPair K hζ S (x.base * y.base) z.base) := by ac_rfl
        _ = _ := by rw [h]; ac_rfl
    · change (x.base * y.base) * z.base = x.base * (y.base * z.base)
      exact mul_assoc x.base y.base z.base
  one_mul x := by
    apply SourceCubicTorus.ext
    · change 1 * x.central * sourceCubicTorusPair K hζ S 1 x.base = x.central
      simp
    · change 1 * x.base = x.base
      exact one_mul x.base
  mul_one x := by
    apply SourceCubicTorus.ext
    · change x.central * 1 * sourceCubicTorusPair K hζ S x.base 1 = x.central
      simp
    · change x.base * 1 = x.base
      exact mul_one x.base
  inv_mul_cancel x := by
    apply SourceCubicTorus.ext
    · change x.central⁻¹ * x.central * sourceCubicTorusPair K hζ S x.base⁻¹ x.base = 1
      rw [inv_mul_cancel, one_mul, sourceCubicTorusPair_inv_self]
    · change x.base⁻¹ * x.base = 1
      exact inv_mul_cancel x.base

def sourceCubicTorusProjection : SourceCubicTorus K hζ S →* SourceCubicTorusBase K S where
  toFun := SourceCubicTorus.base
  map_one' := rfl
  map_mul' _ _ := rfl

def sourceCubicTorusCenter : rootsOfUnity 3 K →* SourceCubicTorus K hζ S where
  toFun z := ⟨z, 1⟩
  map_one' := rfl
  map_mul' z w := by
    apply SourceCubicTorus.ext
    · change z * w = z * w * sourceCubicTorusPair K hζ S 1 1
      simp
    · change 1 = (1 : SourceCubicTorusBase K S) * 1
      exact (one_mul (1 : SourceCubicTorusBase K S)).symm

theorem sourceCubicTorusCenter_injective : Function.Injective (sourceCubicTorusCenter K hζ S) := by
  intro x y h
  exact congrArg SourceCubicTorus.central h

theorem sourceCubicTorusProjection_surjective : Function.Surjective (sourceCubicTorusProjection K hζ S) :=
  fun x => ⟨⟨1, x⟩, rfl⟩

theorem sourceCubicTorus_exact :
    (sourceCubicTorusCenter K hζ S).range = (sourceCubicTorusProjection K hζ S).ker := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hx
    change x.base = 1 at hx
    exact ⟨x.central, SourceCubicTorus.ext K hζ S rfl hx.symm⟩

theorem sourceCubicTorusCenter_commute (z : rootsOfUnity 3 K) (x : SourceCubicTorus K hζ S) :
    Commute (sourceCubicTorusCenter K hζ S z) x := by
  apply SourceCubicTorus.ext
  · change z * x.central * sourceCubicTorusPair K hζ S 1 x.base =
      x.central * z * sourceCubicTorusPair K hζ S x.base 1
    simp [mul_comm]
  · change 1 * x.base = x.base * 1
    exact (one_mul x.base).trans (mul_one x.base).symm

def sourceCubicTorusWeyl : SourceCubicTorus K hζ S ≃* SourceCubicTorus K hζ S where
  toFun x := ⟨x.central, x.base⁻¹⟩
  invFun x := ⟨x.central, x.base⁻¹⟩
  left_inv x := by
    apply SourceCubicTorus.ext
    · rfl
    · exact inv_inv x.base
  right_inv x := by
    apply SourceCubicTorus.ext
    · rfl
    · exact inv_inv x.base
  map_mul' x y := by
    apply SourceCubicTorus.ext
    · change x.central * y.central * sourceCubicTorusPair K hζ S x.base y.base =
        x.central * y.central * sourceCubicTorusPair K hζ S x.base⁻¹ y.base⁻¹
      rw [sourceCubicTorusPair_inv_inv]
    · change (x.base * y.base)⁻¹ = x.base⁻¹ * y.base⁻¹
      exact mul_inv x.base y.base

theorem sourceCubicTorusWeyl_involutive : Function.Involutive (sourceCubicTorusWeyl K hζ S) := by
  intro x
  apply SourceCubicTorus.ext
  · rfl
  · exact inv_inv x.base

def sourceCubicTorusChosenSection (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    chosenB K hζ S₀ →* SourceCubicTorus K hζ (sourceHilbertSet K S₀) where
  toFun b := ⟨1, b⟩
  map_one' := rfl
  map_mul' x y := by
    apply SourceCubicTorus.ext
    · change 1 = 1 * 1 * sourceCubicTorusPair K hζ (sourceHilbertSet K S₀) x y
      rw [sourceCubicTorusPair_chosenB]
      simp
    · rfl

end
end ArtinMatthews
