module

public import ArtinMatthews.SourceKPMinkowskiCuspLattice
public import ArtinMatthews.SourceArchIwasawaCompletion
public import ArtinMatthews.SourceHyperbolicProductMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The actual scaled Minkowski coordinates and the heights form the native
Euclidean product chart. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Module.Free OAI.CubicEisenstein SourceHyperbolicGreen
open scoped NumberField AdeleRing Matrix
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "C" => sourceKPCuspCoordinates K d hd

private def cuspComplexAt (x : I → ℝ) (v : V) : ℂ :=
  ((C).symm x).2 ⟨v, (source_isTotallyComplex K hζ).isComplex v⟩

private def cuspSpatialTriple (z : ℂ) (y : ℝ) : EuclideanSpatial :=
  WithLp.toLp 2 ![z.re, z.im, y]

private theorem cuspSpatialTriple_fst (z : ℂ) (y : ℝ) : cuspSpatialTriple z y 0 = z.re := rfl
private theorem cuspSpatialTriple_snd (z : ℂ) (y : ℝ) : cuspSpatialTriple z y 1 = z.im := rfl
private theorem cuspSpatialTriple_height (z : ℂ) (y : ℝ) : cuspSpatialTriple z y 2 = y := rfl

private def cuspProductLinearEquiv : ((I → ℝ) × (V → ℝ)) ≃ₗ[ℝ] ProductSpace V where
  toFun a v := cuspSpatialTriple (cuspComplexAt K hζ d hd a.1 v) (a.2 v)
  invFun p := (C (0, fun v => (p v.val 0 : ℂ) + (p v.val 1 : ℂ) * Complex.I),
    fun v => p v 2)
  left_inv := by
    intro a
    apply Prod.ext
    · apply (C).symm.injective
      rw [ContinuousLinearEquiv.symm_apply_apply]
      apply Prod.ext
      · funext v
        exact False.elim
          ((InfinitePlace.not_isReal_iff_isComplex.mpr
            ((source_isTotallyComplex K hζ).isComplex v.val)) v.property)
      · funext v
        simp only [cuspSpatialTriple_fst, cuspSpatialTriple_snd, cuspComplexAt]
        exact Complex.re_add_im (((C).symm a.1).2 v)
    · funext v
      exact cuspSpatialTriple_height (cuspComplexAt K hζ d hd a.1 v) (a.2 v)
  right_inv := by
    intro p
    funext v
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext j
    have hC : cuspComplexAt K hζ d hd
          (C (0, fun w => (p w.val 0 : ℂ) + (p w.val 1 : ℂ) * Complex.I)) v =
        (p v 0 : ℂ) + (p v 1 : ℂ) * Complex.I := by
      unfold cuspComplexAt
      rw [ContinuousLinearEquiv.symm_apply_apply]
    change (cuspSpatialTriple (cuspComplexAt K hζ d hd
      (C (0, fun w => (p w.val 0 : ℂ) + (p w.val 1 : ℂ) * Complex.I)) v) (p v 2)) j =
        p v j
    rw [hC]
    fin_cases j <;>
      simp [cuspSpatialTriple_fst, cuspSpatialTriple_snd, cuspSpatialTriple_height, Complex.mul_re,
        Complex.mul_im, Complex.add_re, Complex.add_im]
  map_add' := by
    intro a b
    funext v
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext j
    change (cuspSpatialTriple (cuspComplexAt K hζ d hd (a + b).1 v) ((a + b).2 v)) j =
      (cuspSpatialTriple (cuspComplexAt K hζ d hd a.1 v) (a.2 v)) j +
        (cuspSpatialTriple (cuspComplexAt K hζ d hd b.1 v) (b.2 v)) j
    fin_cases j <;>
      simp [cuspSpatialTriple_fst, cuspSpatialTriple_snd, cuspSpatialTriple_height, cuspComplexAt,
        Complex.add_re, Complex.add_im]
  map_smul' := by
    intro r a
    funext v
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext j
    change (cuspSpatialTriple (cuspComplexAt K hζ d hd (r • a).1 v) ((r • a).2 v)) j =
      r * (cuspSpatialTriple (cuspComplexAt K hζ d hd a.1 v) (a.2 v)) j
    fin_cases j <;>
      simp [cuspSpatialTriple_fst, cuspSpatialTriple_snd, cuspSpatialTriple_height, cuspComplexAt,
        Complex.real_smul, Complex.mul_re, Complex.mul_im, smul_eq_mul]

/-- The literal horizontal and height chart with the actual scaled cusp basis. -/
def sourceKPCuspProductCoordinates : ((I → ℝ) × (V → ℝ)) ≃L[ℝ] ProductSpace V :=
  (cuspProductLinearEquiv K hζ d hd).toContinuousLinearEquiv

theorem sourceKPCuspProductCoordinates_height (x : I → ℝ) (y : V → ℝ) (v : V) :
    sourceKPCuspProductCoordinates K hζ d hd (x, y) v 2 = y v := rfl

private theorem cuspComplexAt_eq_arch (x : I → ℝ) (v : V) :
    cuspComplexAt K hζ d hd x v =
      sourceKPArchComplexEquiv K hζ v ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm ((C).symm x) v) := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  have h := congrArg (fun z : mixedEmbedding.mixedSpace K =>
    z.2 ⟨v, (source_isTotallyComplex K hζ).isComplex v⟩) (e.apply_symm_apply ((C).symm x))
  exact h.symm

/-- The horizontal real and imaginary coordinates use the same completion
equivalence as the actual adelic upper section. -/
theorem sourceKPCuspProductCoordinates_apply_arch (x : I → ℝ) (y : V → ℝ) (v : V) :
    sourceKPCuspProductCoordinates K hζ d hd (x, y) v =
      WithLp.toLp 2 ![
        (sourceKPArchComplexEquiv K hζ v ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm ((C).symm x) v)).re,
        (sourceKPArchComplexEquiv K hζ v ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm ((C).symm x) v)).im,
        y v] := by
  change cuspSpatialTriple (cuspComplexAt K hζ d hd x v) (y v) = _
  simp only [cuspComplexAt_eq_arch, cuspSpatialTriple]

end
end ArtinMatthews
