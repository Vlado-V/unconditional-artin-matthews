module

public import ArtinMatthews.SourceCubicLocalUnitTorus


set_option backward.privateInPublic true
@[expose] public section

/-! The determinant-modified c=2 torus cocycle in the source's actual
Hilbert normalization. The cubic orientation is explicit: its inverse
square equals the source H6 squared. Scalar splitting and centrality
are proved from cubic torsion, not assumed from a metaplectic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] in
theorem sourceCubicRoot_cube (u : rootsOfUnity 3 K) : u ^ 3 = 1 := by
  apply Subtype.ext
  exact (mem_rootsOfUnity 3 (u : Kˣ)).mp u.property

def sourceKPCubicHilbert :
    SourceCubicTorusBase K S →* (SourceCubicTorusBase K S →* rootsOfUnity 3 K) :=
  (sourceCubicTorusPair K hζ S)⁻¹

theorem sourceKPCubicHilbert_skew (x y : SourceCubicTorusBase K S) :
    sourceKPCubicHilbert K hζ S x y = (sourceKPCubicHilbert K hζ S y x)⁻¹ := by
  change (sourceCubicTorusPair K hζ S x y)⁻¹ = ((sourceCubicTorusPair K hζ S y x)⁻¹)⁻¹
  rw [sourceCubicTorusPair_skew]

def sourceCubicKPTorusSigma (x y : SourceCubicTorusBase K S × SourceCubicTorusBase K S) :
    rootsOfUnity 3 K :=
  sourceKPCubicHilbert K hζ S x.1 y.2 *
    sourceKPCubicHilbert K hζ S (x.1 * x.2) (y.1 * y.2) ^ 2

theorem sourceCubicKPTorusSigma_cocycle
    (x y z : SourceCubicTorusBase K S × SourceCubicTorusBase K S) :
    sourceCubicKPTorusSigma K hζ S x y * sourceCubicKPTorusSigma K hζ S (x * y) z =
      sourceCubicKPTorusSigma K hζ S y z * sourceCubicKPTorusSigma K hζ S x (y * z) := by
  apply Additive.ofMul.injective
  simp only [sourceCubicKPTorusSigma, Prod.fst_mul, Prod.snd_mul, map_mul,
    MonoidHom.mul_apply, ofMul_mul, ofMul_pow]
  abel

theorem sourceCubicKPTorusSigma_scalar_pair (a b : SourceCubicTorusBase K S) :
    sourceCubicKPTorusSigma K hζ S (a, a) (b, b) = 1 := by
  have h := sourceCubicRoot_cube K (sourceKPCubicHilbert K hζ S a b)
  unfold sourceCubicKPTorusSigma
  simp only [map_mul, MonoidHom.mul_apply]
  calc
    _ = (sourceKPCubicHilbert K hζ S a b) ^ 9 := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow]
      abel
    _ = 1 := by rw [show 9 = 3 * 3 by decide, pow_mul, h, one_pow]

theorem sourceCubicKPTorusSigma_scalar_central (a : SourceCubicTorusBase K S)
    (x : SourceCubicTorusBase K S × SourceCubicTorusBase K S) :
    sourceCubicKPTorusSigma K hζ S (a, a) x = sourceCubicKPTorusSigma K hζ S x (a, a) := by
  have hratio : sourceCubicKPTorusSigma K hζ S (a, a) x /
      sourceCubicKPTorusSigma K hζ S x (a, a) =
        (sourceKPCubicHilbert K hζ S a (x.1 * x.2)) ^ 9 := by
    unfold sourceCubicKPTorusSigma
    rw [sourceKPCubicHilbert_skew K hζ S x.1 a,
      sourceKPCubicHilbert_skew K hζ S (x.1 * x.2) (a * a)]
    simp only [map_mul, MonoidHom.mul_apply]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div]
    abel
  apply div_eq_one.mp
  rw [hratio, show 9 = 3 * 3 by decide, pow_mul, sourceCubicRoot_cube]

theorem sourceCubicKPTorusSigma_rank_one (a b : SourceCubicTorusBase K S) :
    sourceCubicKPTorusSigma K hζ S (a, 1) (b, 1) = sourceCubicTorusPair K hζ S a b := by
  have h := sourceCubicRoot_cube K (sourceCubicTorusPair K hζ S a b)
  unfold sourceCubicKPTorusSigma
  rw [show a * 1 = a from mul_one a, show b * 1 = b from mul_one b, map_one, one_mul]
  change ((sourceCubicTorusPair K hζ S a b)⁻¹) ^ 2 = _
  calc
    _ = ((sourceCubicTorusPair K hζ S a b)⁻¹) ^ 2 *
        (sourceCubicTorusPair K hζ S a b) ^ 3 := by rw [h, mul_one]
    _ = _ := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv]
      abel

end
end ArtinMatthews
