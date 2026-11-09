module

public import ArtinMatthews.SourceSLocalIdeleLift
public import ArtinMatthews.SourceKPFiniteAdeleTorus


set_option backward.privateInPublic true
@[expose] public section

/-! The exterior part of a principal idèle has its original coordinates
off S. Disjointness from an S-local idèle removes the finite torus phase. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "ι" => IdeleGroup.unitEmbedding (𝓞 K) K

def sourceSLocalExteriorIdele (a : Kˣ) : IdeleGroup (𝓞 K) K :=
  (sourceSLocalIdeleLift K S (sWholeDiagonal K S a))⁻¹ * ι a

theorem sourceSLocalExteriorIdele_mul_retained (a : Kˣ) :
    sourceSLocalExteriorIdele K S a * sourceSLocalIdeleLift K S (sWholeDiagonal K S a) = ι a := by
  calc
    _ = ι a * ((sourceSLocalIdeleLift K S (sWholeDiagonal K S a))⁻¹ *
        sourceSLocalIdeleLift K S (sWholeDiagonal K S a)) := by
      unfold sourceSLocalExteriorIdele
      ac_rfl
    _ = _ := by rw [inv_mul_cancel,mul_one]

theorem sourceSLocalExteriorIdele_infinite_unit (a : Kˣ) :
    sourceKPIdeleInfiniteUnit K (sourceSLocalExteriorIdele K S a) = 1 := by
  have h : sourceKPIdeleInfiniteUnit K (ι a) = MulEquiv.piUnits.symm (sWholeDiagonal K S a).1 := by
    apply Units.ext
    funext w
    rfl
  have hr : sourceKPIdeleInfiniteUnit K (sourceSLocalIdeleLift K S (sWholeDiagonal K S a)) =
      sourceKPIdeleInfiniteUnit K (ι a) :=
    (sourceSLocalIdeleLift_infinite_unit K S (sWholeDiagonal K S a)).trans h.symm
  rw [sourceSLocalExteriorIdele,map_mul,map_inv,hr,inv_mul_cancel]

theorem sourceSLocalExteriorIdele_finite_in (a : Kˣ) (P : S) :
    sourceKPIdeleFiniteCoordinate K P.val (sourceSLocalExteriorIdele K S a) = 1 := by
  have h : sourceKPIdeleFiniteCoordinate K P.val (ι a) = (sWholeDiagonal K S a).2 P := Units.ext rfl
  rw [sourceSLocalExteriorIdele,map_mul,map_inv,sourceSLocalIdeleLift_finite_in,h,inv_mul_cancel]

theorem sourceSLocalExteriorIdele_finite_out (a : Kˣ)
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ S) :
    sourceKPIdeleFiniteCoordinate K P (sourceSLocalExteriorIdele K S a) =
      sourceKPIdeleFiniteCoordinate K P (ι a) := by
  rw [sourceSLocalExteriorIdele,map_mul,map_inv,sourceSLocalIdeleLift_finite_out K S _ P hP,
    inv_one,one_mul]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "C" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "d" => sourceKPDiagonalHom 𝔸ᶠ[K]
local notation "μ" => sourceKPAdeleMultiplier K hζ
local notation "f" => sourceKPIdeleFiniteUnit K

theorem sourceKPFiniteAdeleProjectiveDiagonalLift_mul_center (u v : 𝔸ᶠ[K]ˣ) :
    D u * D v = C (μ (d u) (d v)) * D (u * v) := by
  unfold sourceKPFiniteAdeleProjectiveDiagonalLift sourceKPFiniteAdeleProjectiveCenter
  simp only [MonoidHom.comp_apply, ← map_mul]
  apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
  apply SourceKPFiniteAdeleCover.ext
  · change 1 * 1 * μ (d u) (d v) = μ (d u) (d v) * 1 * μ 1 (d (u * v))
    simp only [sourceKPAdeleMultiplier_one_left,one_mul,mul_one]
  · change d u * d v = 1 * d (u * v)
    rw [map_mul,one_mul]

theorem sourceSLocalExteriorDiagonal_mul (a : Kˣ) (x : SWholeUnits K S) :
    D (f (sourceSLocalExteriorIdele K S a)) * D (f (sourceSLocalIdeleLift K S x)) =
      D (f (sourceSLocalExteriorIdele K S a * sourceSLocalIdeleLift K S x)) := by
  rw [map_mul,sourceKPFiniteAdeleProjectiveDiagonalLift_mul_center]
  suffices h : μ (d (f (sourceSLocalExteriorIdele K S a))) (d (f (sourceSLocalIdeleLift K S x))) = 1 by
    rw [h,map_one,one_mul]
  rw [sourceKPAdeleMultiplier]
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier_diagonal]
  change (sourceKPRootsTransport K hζ P).symm
    (sourceFiniteKPHilbert K hζ P
      (sourceKPIdeleFiniteCoordinate K P (sourceSLocalExteriorIdele K S a))
      (sourceKPIdeleFiniteCoordinate K P (sourceSLocalIdeleLift K S x)) ^ 2) = 1
  by_cases hP : P ∈ S
  · rw [sourceSLocalExteriorIdele_finite_in K S a ⟨P,hP⟩]
    simp only [map_one,MonoidHom.one_apply,one_pow]
  · rw [sourceSLocalIdeleLift_finite_out K S x P hP]
    simp only [map_one,one_pow]

end
end ArtinMatthews
