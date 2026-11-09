module

public import ArtinMatthews.SourceSLocalExteriorDiagonal
public import ArtinMatthews.SourceKPReflectionWeyl
public import ArtinMatthews.SourceKPAdelicWeyl


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rational signed Weyl element reflects the retained
idèle and contributes precisely the finite product of its retained phases. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "ι" => IdeleGroup.unitEmbedding (𝓞 K) K
local notation "R" => sourceKPAdelicProjectiveRationalLift K hζ
local notation "D" => sourceKPAdelicProjectiveDiagonalLift K hζ
local notation "W" => sourceKPAdelicProjectiveWeyl K hζ
local notation "d" => sourceKPDiagonalHom 𝔸ᶠ[K]
local notation "f" => sourceKPIdeleFiniteUnit K
local notation "Df" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "C" => sourceKPFiniteAdeleProjectiveCenter K hζ

def sourceSLocalWeylPhase (b : Kˣ) (x : SWholeUnits K S) : rootsOfUnity 3 K :=
  ∏ P ∈ S, sourceKPAdeleLocalMultiplier K hζ (d (f (ι ((b⁻¹)^2))))
    (d (f (sourceSLocalIdeleLift K S x)⁻¹)) P

theorem sourceSLocalWeylPhase_eq_hilbert_product (b : Kˣ) (x : SWholeUnits K S) :
    sourceSLocalWeylPhase K S hζ b x =
      ∏ P : S, (sourceKPRootsTransport K hζ P.val).symm
        (sourceFiniteKPHilbert K hζ P.val ((sWholeDiagonal K S ((b⁻¹)^2)).2 P)
          ((x.2 P)⁻¹) ^ 2) := by
  unfold sourceSLocalWeylPhase
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro P _
  rw [sourceKPAdeleLocalMultiplier_diagonal]
  have ha : sourceKPIdeleFiniteCoordinate K P.val (ι ((b⁻¹)^2)) =
      (sWholeDiagonal K S ((b⁻¹)^2)).2 P := Units.ext rfl
  change (sourceKPRootsTransport K hζ P.val).symm
    (sourceFiniteKPHilbert K hζ P.val (sourceKPIdeleFiniteCoordinate K P.val (ι ((b⁻¹)^2)))
      (sourceKPIdeleFiniteCoordinate K P.val (sourceSLocalIdeleLift K S x)⁻¹) ^ 2) = _
  rw [ha,map_inv,sourceSLocalIdeleLift_finite_in]

private theorem sourceSLocalWeylPhase_retained_multiplier (b : Kˣ) (x : SWholeUnits K S) :
    sourceKPAdeleMultiplier K hζ (d (f (sourceSLocalIdeleLift K S (sWholeDiagonal K S ((b⁻¹)^2)))))
      (d (f (sourceSLocalIdeleLift K S x⁻¹))) = sourceSLocalWeylPhase K S hζ b x := by
  let a := (b⁻¹)^2
  let y := sourceSLocalIdeleLift K S (sWholeDiagonal K S a)
  let z := sourceSLocalIdeleLift K S x⁻¹
  let M (P : HeightOneSpectrum (𝓞 K)) := sourceKPAdeleLocalMultiplier K hζ (d (f y)) (d (f z)) P
  have hs : Function.mulSupport M ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro P h
    by_contra hP
    apply h
    unfold M
    rw [sourceKPAdeleLocalMultiplier_diagonal]
    change (sourceKPRootsTransport K hζ P).symm
      (sourceFiniteKPHilbert K hζ P (sourceKPIdeleFiniteCoordinate K P y)
        (sourceKPIdeleFiniteCoordinate K P (sourceSLocalIdeleLift K S x⁻¹)) ^ 2) = 1
    rw [sourceSLocalIdeleLift_finite_out K S x⁻¹ P hP]
    simp only [map_one,one_pow]
  change (∏ᶠ P, M P) = _
  rw [finprod_eq_prod_of_mulSupport_subset M hs,sourceSLocalWeylPhase,
    ← map_inv (sourceSLocalIdeleLift K S)]
  apply Finset.prod_congr rfl
  intro P hP
  have ha : sourceKPIdeleFiniteCoordinate K P (ι a) =
      (sWholeDiagonal K S a).2 ⟨P,hP⟩ := Units.ext rfl
  have hy : sourceKPIdeleFiniteCoordinate K P y = sourceKPIdeleFiniteCoordinate K P (ι a) :=
    (sourceSLocalIdeleLift_finite_in K S (sWholeDiagonal K S a) ⟨P,hP⟩).trans ha.symm
  simp only [M,sourceKPAdeleLocalMultiplier_diagonal]
  change (sourceKPRootsTransport K hζ P).symm
      (sourceFiniteKPHilbert K hζ P (sourceKPIdeleFiniteCoordinate K P y)
        (sourceKPIdeleFiniteCoordinate K P z) ^ 2) =
    (sourceKPRootsTransport K hζ P).symm
      (sourceFiniteKPHilbert K hζ P (sourceKPIdeleFiniteCoordinate K P (ι a))
        (sourceKPIdeleFiniteCoordinate K P z) ^ 2)
  rw [hy]

private theorem rationalReflectionWeyl_factor (b : Kˣ) :
    R (sourceKPReflectionWeyl K b) = D (ι ((b⁻¹)^2)) * R (sourceKPReflectionWeyl K 1) := by
  have hb : sourceKPReflectionWeyl K b =
      sourceKPProjectiveDiagonalHom K ((b⁻¹)^2) * sourceKPReflectionWeyl K 1 := by
    rw [sourceKPReflectionWeyl_eq K b,sourceKPReflectionWeyl_eq K 1]
    simp only [inv_one,one_pow,map_one,one_mul,mul_assoc]
  rw [hb,map_mul,sourceKPAdelicProjectiveRationalLift_diagonal]

private theorem rationalReflectionWeyl_one_diagonal (u : IdeleGroup (𝓞 K) K) :
    R (sourceKPReflectionWeyl K 1) * D u = D u⁻¹ * R (sourceKPReflectionWeyl K 1) := by
  have hneg : (-1 : Kˣ)^3 = -1 := by
    apply Units.ext
    norm_num
  have hc : Commute (D (ι (-1))) (D u⁻¹) := by
    have h := sourceKPAdelicProjectiveDiagonalLift_cube_commute K hζ (ι (-1)) u⁻¹
    rwa [← map_pow ι,hneg] at h
  have hr : R (sourceKPReflectionWeyl K 1) = D (ι (-1)) * W := by
    simp only [sourceKPReflectionWeyl_eq K 1,inv_one,one_pow,map_one,one_mul,map_mul,
      sourceKPAdelicProjectiveRationalLift_diagonal,sourceKPAdelicProjectiveWeyl]
  rw [hr,mul_assoc,sourceKPAdelicProjectiveWeyl_diagonal,← mul_assoc,hc.eq,mul_assoc]

theorem sourceSLocalFiniteWeyl_diagonal (b : Kˣ) (x : SWholeUnits K S) :
    (R (sourceKPReflectionWeyl K b)).2 * (sourceSLocalProjectiveDiagonalLift K S hζ x).2 =
      C (sourceSLocalWeylPhase K S hζ b x) *
        (D (sourceSLocalExteriorIdele K S ((b⁻¹)^2))).2 *
        (sourceSLocalProjectiveDiagonalLift K S hζ (sWholeDiagonal K S ((b⁻¹)^2)*x⁻¹)).2 *
        (R (sourceKPReflectionWeyl K 1)).2 := by
  let a := (b⁻¹)^2
  let a₀ := sWholeDiagonal K S a
  let xS := sourceSLocalIdeleLift K S x
  let E := sourceSLocalExteriorIdele K S a
  let r₁ := (R (sourceKPReflectionWeyl K 1)).2
  let ω := sourceSLocalWeylPhase K S hζ b x
  let L := sourceSLocalIdeleLift K S
  change (R (sourceKPReflectionWeyl K b)).2 * Df (f xS) =
    C ω * Df (f E) * Df (f (L (a₀*x⁻¹))) * r₁
  have hb : (R (sourceKPReflectionWeyl K b)).2 = Df (f (ι a)) * r₁ :=
    congrArg Prod.snd (rationalReflectionWeyl_factor K hζ b)
  have hw : r₁ * Df (f xS) = Df (f (L x⁻¹)) * r₁ := by
    rw [map_inv L]
    exact congrArg Prod.snd (rationalReflectionWeyl_one_diagonal K hζ xS)
  have he : Df (f E) * Df (f (L a₀)) = Df (f (ι a)) := by
    exact (sourceSLocalExteriorDiagonal_mul K S hζ a a₀).trans
      (congrArg (fun t => Df (f t)) (sourceSLocalExteriorIdele_mul_retained K S a))
  have hprod : Df (f (L a₀)) * Df (f (L x⁻¹)) = C ω * Df (f (L (a₀*x⁻¹))) := by
    rw [sourceKPFiniteAdeleProjectiveDiagonalLift_mul_center, map_mul L, map_mul f]
    exact congrArg (fun z => C z * Df (f (L a₀) * f (L x⁻¹)))
      (sourceSLocalWeylPhase_retained_multiplier K S hζ b x)
  calc
    _ = Df (f (ι a)) * (r₁ * Df (f xS)) := by rw [hb,mul_assoc]
    _ = Df (f E) * (Df (f (L a₀)) * Df (f (L x⁻¹))) * r₁ := by
      rw [hw,← he]
      simp only [mul_assoc]
    _ = (Df (f E) * C ω) * Df (f (L (a₀*x⁻¹))) * r₁ := by
      rw [hprod]
      simp only [mul_assoc]
    _ = _ := by rw [(sourceKPFiniteAdeleProjectiveCenter_commute K hζ ω (Df (f E))).eq]

end
end ArtinMatthews
