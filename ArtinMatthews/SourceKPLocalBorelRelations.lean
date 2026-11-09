module

public import ArtinMatthews.SourceKPLocalBorelEmbedding
public import ArtinMatthews.SourceKPTameParametricAction


set_option backward.privateInPublic true
@[expose] public section

/-! Exact diagonal commutators and upper-root action for the local
Borel receiver, retaining the actual cubic Hilbert factors. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPLocalBorelDiagonal_mul (x y : (P.adicCompletion K)ˣ) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P x * sourceFiniteKPProjectiveBorelDiagonal K hζ P y =
      sourceFiniteKPProjectiveBorelCenter K hζ P (sourceFiniteKPHilbert K hζ P x y ^ 2) *
        sourceFiniteKPProjectiveBorelDiagonal K hζ P (x*y) := by
  apply Subtype.ext
  exact sourceFiniteKP2ProjectiveLift_diagonal_mul K hζ P x y

theorem sourceKPLocalBorelDiagonal_commutator (x y : (P.adicCompletion K)ˣ) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P x * sourceFiniteKPProjectiveBorelDiagonal K hζ P y =
      sourceFiniteKPProjectiveBorelCenter K hζ P
        (sourceFiniteKPHilbert K hζ P x y ^ 2 / sourceFiniteKPHilbert K hζ P y x ^ 2) *
        (sourceFiniteKPProjectiveBorelDiagonal K hζ P y * sourceFiniteKPProjectiveBorelDiagonal K hζ P x) := by
  apply Subtype.ext
  change sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal x) *
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal y) =
    sourceFiniteKP2ProjectiveCenter K hζ P
      (sourceFiniteKPHilbert K hζ P x y ^ 2 / sourceFiniteKPHilbert K hζ P y x ^ 2) *
      (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal y) *
        sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal x))
  rw [sourceFiniteKP2ProjectiveLift_diagonal_mul, sourceFiniteKP2ProjectiveLift_diagonal_mul,
    ← mul_assoc, ← map_mul, div_mul_cancel, mul_comm y x]

theorem sourceKPAdelicLocalBorel_upper (x : P.adicCompletion K) :
    sourceKPAdelicLocalBorel K hζ P (sourceFiniteKPProjectiveBorelUpper K hζ P x) =
      sourceKPAdelicBorelCoordinatesEquiv K hζ ((0, sourceKPFiniteAdditiveSingle K P x), 1) := by
  apply Subtype.ext
  change sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x)) =
    sourceKPAdelicUpperLift K hζ (0, sourceKPFiniteAdditiveSingle K P x) * 1
  rw [sourceKPAdelicLocalProjective_upper, mul_one]

theorem sourceKPAdelicLocalBorelRepresentation_upper (s : ℂ) (x : P.adicCompletion K)
    (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicLocalBorelRepresentation K hζ P s
      (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v := by
  change sourceKPAdelicNormalizedBorelRepresentation K hζ s
    (sourceKPAdelicLocalBorel K hζ P (sourceFiniteKPProjectiveBorelUpper K hζ P x)) v = v
  rw [sourceKPAdelicLocalBorel_upper]
  let a : 𝔸[K] := (0, sourceKPFiniteAdditiveSingle K P x)
  let b := sourceKPAdelicBorelCoordinatesEquiv K hζ (a, 1)
  have hp : sourceKPAdelicBorelTorusProjection K hζ b = 1 :=
    sourceKPAdelicBorelTorusProjection_coordinates K hζ a 1
  have hd : sourceKPAdelicBorelModularHalf K hζ b = 1 := by
    change (sourceKPIdeleComplexNorm K (1/2 : ℂ)
      (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b)) : ℂ) = 1
    rw [hp, map_one, map_one, Units.val_one]
  change sourceKPAdelicBorelModularHalf K hζ b •
    sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicBorelTorusProjection K hζ b) v = v
  rw [hd, hp, map_one, one_smul]
  rfl

end
end ArtinMatthews
