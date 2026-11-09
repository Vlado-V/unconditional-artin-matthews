module

public import ArtinMatthews.SourceKubotaRationalCoordinates
public import ArtinMatthews.SourceFiniteKPMultipliers
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertProductFormula


set_option backward.privateInPublic true
@[expose] public section

/-! Rational Kubota multipliers have finite support and product one
under the actual coherent cubic Hilbert symbols. All three symbol
factors, including the determinant twist, are transported from the
rational matrices before applying global reciprocity. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open scoped NumberField MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPRootsTransport (P : HeightOneSpectrum (𝓞 K)) :
    rootsOfUnity 3 K ≃* rootsOfUnity 3 (P.adicCompletion K) :=
  rootsOfUnityEquivOfPrimitiveRoots (algebraMap K (P.adicCompletion K)).injective
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ))

def sourceRationalKPHilbert (a b : Kˣ) (P : HeightOneSpectrum (𝓞 K)) : rootsOfUnity 3 K :=
  GlobalHilbertPairingFamily.finiteFactor K
    (finitePlaceAdicHilbertPairingFamily K 3
      (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)))
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)) P a b

theorem sourceRationalKPHilbert_hasFiniteMulSupport (a b : Kˣ) :
    Function.HasFiniteMulSupport (sourceRationalKPHilbert K hζ a b) :=
  (finitePlaceAdicHilbertPairingFamily_productFormula K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ))).2.1 a b

theorem sourceRationalKPHilbert_finprod (a b : Kˣ) :
    ∏ᶠ P, sourceRationalKPHilbert K hζ a b P = 1 := by
  have h := (finitePlaceAdicHilbertPairingFamily_productFormula K 3
    (sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ))).2.2 a b
  have hinf : (∏ v : InfinitePlace K, globalInfinitePlaceHilbertSymbol K 3 v a b) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    unfold globalInfinitePlaceHilbertSymbol
    split
    next he => norm_num at he
    next => rfl
  rw [hinf, one_mul] at h
  exact h

def sourceFiniteKP2RationalMultiplier (g h : GL (Fin 2) K)
    (P : HeightOneSpectrum (𝓞 K)) : rootsOfUnity 3 K :=
  (sourceKPRootsTransport K hζ P).symm
    (sourceFiniteKP2Multiplier K hζ P (GeneralLinearGroup.map (algebraMap K _) g)
      (GeneralLinearGroup.map (algebraMap K _) h))

theorem sourceFiniteKP2RationalMultiplier_factor (g h : GL (Fin 2) K)
    (P : HeightOneSpectrum (𝓞 K)) :
    sourceFiniteKP2RationalMultiplier K hζ g h P =
      sourceRationalKPHilbert K hζ (sourceKubotaRatioLeft g h) (sourceKubotaRatioRight g h) P *
        sourceRationalKPHilbert K hζ (GeneralLinearGroup.det g) (GeneralLinearGroup.det h) P ^ 2 := by
  let f := algebraMap K (P.adicCompletion K)
  let e := sourceKPRootsTransport K hζ P
  let B := sourceFiniteKPHilbert K hζ P
  change e.symm (B (sourceKubotaRatioLeft (GeneralLinearGroup.map f g) (GeneralLinearGroup.map f h))
      (sourceKubotaRatioRight (GeneralLinearGroup.map f g) (GeneralLinearGroup.map f h)) *
      B (GeneralLinearGroup.det (GeneralLinearGroup.map f g))
        (GeneralLinearGroup.det (GeneralLinearGroup.map f h)) ^ 2) = _
  rw [sourceKubotaRatioLeft_map, sourceKubotaRatioRight_map, GeneralLinearGroup.map_det,
    GeneralLinearGroup.map_det, map_mul, map_pow]
  rfl

theorem sourceFiniteKP2RationalMultiplier_hasFiniteMulSupport (g h : GL (Fin 2) K) :
    Function.HasFiniteMulSupport (sourceFiniteKP2RationalMultiplier K hζ g h) := by
  have he := funext (sourceFiniteKP2RationalMultiplier_factor K hζ g h)
  rw [he]
  exact (sourceRationalKPHilbert_hasFiniteMulSupport K hζ _ _).mul
    ((sourceRationalKPHilbert_hasFiniteMulSupport K hζ _ _).pow 2)

theorem sourceFiniteKP2RationalMultiplier_finprod (g h : GL (Fin 2) K) :
    ∏ᶠ P, sourceFiniteKP2RationalMultiplier K hζ g h P = 1 := by
  let A := sourceRationalKPHilbert K hζ (sourceKubotaRatioLeft g h) (sourceKubotaRatioRight g h)
  let D := sourceRationalKPHilbert K hζ (GeneralLinearGroup.det g) (GeneralLinearGroup.det h)
  have hA : Function.HasFiniteMulSupport A := sourceRationalKPHilbert_hasFiniteMulSupport K hζ _ _
  have hD : Function.HasFiniteMulSupport D := sourceRationalKPHilbert_hasFiniteMulSupport K hζ _ _
  have hD' : Function.HasFiniteMulSupport (fun P => D P ^ (2 : ℕ)) := hD.pow 2
  calc
    _ = ∏ᶠ P, A P * D P ^ 2 := finprod_congr (sourceFiniteKP2RationalMultiplier_factor K hζ g h)
    _ = (∏ᶠ P, A P) * (∏ᶠ P, D P) ^ 2 := by
      rw [finprod_mul_distrib hA hD', ← finprod_pow hD 2]
    _ = 1 := by simp only [A, D, sourceRationalKPHilbert_finprod, one_pow, one_mul]

end
end ArtinMatthews
