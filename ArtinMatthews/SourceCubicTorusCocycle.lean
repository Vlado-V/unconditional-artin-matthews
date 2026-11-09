module

public import ArtinMatthews.AllowedGeneratorBase


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic torus cocycle required by source03. It is the
square of the source-normalized sextic Hilbert form on the literal
S-local quotient. The chosen isotropic complement is the constructed
arithmetic one. No representation or rational automorphy is assumed. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sourceSexticRootSquare : rootsOfUnity 6 K →* rootsOfUnity 3 K where
  toFun u := ⟨(u : Kˣ) ^ 2, by
    rw [mem_rootsOfUnity, ← pow_mul]
    exact (mem_rootsOfUnity 6 (u : Kˣ)).mp u.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' u v := by apply Subtype.ext; simp [mul_pow]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev SourceCubicTorusBase := SLocalRingPowerClasses K 6 S

def sourceCubicTorusPair :
    SourceCubicTorusBase K S →* (SourceCubicTorusBase K S →* rootsOfUnity 3 K) where
  toFun x := (sourceSexticRootSquare K).comp (paperSourceHilbertForm K hζ S x)
  map_one' := by
    apply MonoidHom.ext
    intro y
    change sourceSexticRootSquare K (paperSourceHilbertForm K hζ S 1 y) = 1
    rw [map_one, MonoidHom.one_apply, map_one]
  map_mul' x y := by
    apply MonoidHom.ext
    intro z
    change sourceSexticRootSquare K (paperSourceHilbertForm K hζ S (x * y) z) =
      sourceSexticRootSquare K (paperSourceHilbertForm K hζ S x z) *
        sourceSexticRootSquare K (paperSourceHilbertForm K hζ S y z)
    rw [map_mul, MonoidHom.mul_apply, map_mul]

theorem sourceCubicTorusPair_val (x y : SourceCubicTorusBase K S) :
    (sourceCubicTorusPair K hζ S x y : Kˣ) =
      (paperSourceHilbertForm K hζ S x y : Kˣ) ^ 2 := rfl

theorem sourceCubicTorusPair_diag (x : SourceCubicTorusBase K S) :
    sourceCubicTorusPair K hζ S x x = 1 := by
  change sourceSexticRootSquare K (paperSourceHilbertForm K hζ S x x) = 1
  rw [paperSourceHilbertForm_diag_eq_one, map_one]

theorem sourceCubicTorusPair_skew (x y : SourceCubicTorusBase K S) :
    sourceCubicTorusPair K hζ S x y = (sourceCubicTorusPair K hζ S y x)⁻¹ := by
  change sourceSexticRootSquare K (sourceRingHilbertForm K hζ S y x) = _
  rw [sourceRingHilbertForm_skew, map_inv]
  rfl

theorem sourceCubicTorusPair_cocycle (x y z : SourceCubicTorusBase K S) :
    sourceCubicTorusPair K hζ S x y * sourceCubicTorusPair K hζ S (x * y) z =
      sourceCubicTorusPair K hζ S y z * sourceCubicTorusPair K hζ S x (y * z) := by
  simp only [map_mul, MonoidHom.mul_apply, mul_comm, mul_left_comm]

theorem sourceCubicTorusPair_inv_self (x : SourceCubicTorusBase K S) :
    sourceCubicTorusPair K hζ S x⁻¹ x = 1 := by
  rw [map_inv, MonoidHom.inv_apply, sourceCubicTorusPair_diag, inv_one]

theorem sourceCubicTorusPair_inv_inv (x y : SourceCubicTorusBase K S) :
    sourceCubicTorusPair K hζ S x⁻¹ y⁻¹ = sourceCubicTorusPair K hζ S x y := by
  have h := map_inv (sourceCubicTorusPair K hζ S) x
  rw [h, MonoidHom.inv_apply, map_inv, inv_inv]

theorem sourceCubicTorusPair_chosenB
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (x y : chosenB K hζ S₀) :
    sourceCubicTorusPair K hζ (sourceHilbertSet K S₀) x y = 1 := by
  change sourceSexticRootSquare K
    (paperSourceHilbertForm K hζ (sourceHilbertSet K S₀) x y) = 1
  rw [chosenB_isotropic K hζ S₀ x x.property y y.property, map_one]

end
end ArtinMatthews
