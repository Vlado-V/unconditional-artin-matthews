module

public import ArtinMatthews.SourceArchOnlyIdele
public import ArtinMatthews.SourceKPAdeleLocalCover
public import ArtinMatthews.SourceKPAdelicUnitTorus
public import ArtinMatthews.SLocalLogarithm


set_option backward.privateInPublic true
@[expose] public section

/-! The idèle attached to the literal S-local product has the given
completion coordinates on S and at infinity, and coordinate one elsewhere. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing BigOperators MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceSLocalIdeleLift : SWholeUnits K S →* IdeleGroup (𝓞 K) K where
  toFun x := sourceArchOnlyIdele K (MulEquiv.piUnits.symm x.1) *
    ∏ P : S, IdeleGroup.ofAdicCompletion (𝓞 K) K P.val (x.2 P)
  map_one' := by
    change sourceArchOnlyIdele K (MulEquiv.piUnits.symm 1) *
      (∏ P : S, IdeleGroup.ofAdicCompletion (𝓞 K) K P.val 1) = 1
    simp only [map_one, Finset.prod_const_one, mul_one]
    exact (sourceArchOnlyIdele K).map_one
  map_mul' x y := by
    let arch : (∀ w : InfinitePlace K, w.Completionˣ) →* IdeleGroup (𝓞 K) K :=
      (sourceArchOnlyIdele K).comp MulEquiv.piUnits.symm.toMonoidHom
    change arch (x.1*y.1) *
      (∏ P : S, IdeleGroup.ofAdicCompletion (𝓞 K) K P.val (x.2 P*y.2 P)) =
      (arch x.1 * ∏ P : S, IdeleGroup.ofAdicCompletion (𝓞 K) K P.val (x.2 P)) *
        (arch y.1 * ∏ P : S, IdeleGroup.ofAdicCompletion (𝓞 K) K P.val (y.2 P))
    simp only [map_mul, Finset.prod_mul_distrib]
    ac_rfl

theorem sourceSLocalIdeleLift_infinite_unit (x : SWholeUnits K S) :
    sourceKPIdeleInfiniteUnit K (sourceSLocalIdeleLift K S x) = MulEquiv.piUnits.symm x.1 := by
  have h (P : S) : sourceKPIdeleInfiniteUnit K
      (IdeleGroup.ofAdicCompletion (𝓞 K) K P.val (x.2 P)) = 1 := by
    apply Units.ext
    rfl
  change sourceKPIdeleInfiniteUnit K (sourceArchOnlyIdele K (MulEquiv.piUnits.symm x.1) *
    ∏ P : S, IdeleGroup.ofAdicCompletion (𝓞 K) K P.val (x.2 P)) = _
  simp only [map_mul, map_prod, h, Finset.prod_const_one, mul_one]
  exact sourceArchOnlyIdele_infinite K (MulEquiv.piUnits.symm x.1)

theorem sourceSLocalIdeleLift_arch (x : SWholeUnits K S) (w : InfinitePlace K) :
    sourceKPIdeleInfiniteCoordinate K w (sourceSLocalIdeleLift K S x) = x.1 w := by
  change Units.map (sourceKPInfiniteCoordinate K w).toMonoidHom
    (sourceKPIdeleInfiniteUnit K (sourceSLocalIdeleLift K S x)) = _
  rw [sourceSLocalIdeleLift_infinite_unit]
  exact Units.ext rfl

private theorem sourceSLocalIdeleLift_finite_product (x : SWholeUnits K S)
    (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPIdeleFiniteCoordinate K P (sourceSLocalIdeleLift K S x) =
      ∏ Q : S, Units.map (sourceKPAdeleEval K P).toMonoidHom
        (sourceKPAdeleLocalUnit K Q.val (x.2 Q)) := by
  change Units.map (sourceKPAdeleEval K P).toMonoidHom
    (sourceKPIdeleFiniteUnit K (sourceArchOnlyIdele K (MulEquiv.piUnits.symm x.1) *
      ∏ Q : S, IdeleGroup.ofAdicCompletion (𝓞 K) K Q.val (x.2 Q))) = _
  simp only [map_mul, map_prod, sourceKPAdeleLocalUnit]
  rw [sourceArchOnlyIdele_finite K (MulEquiv.piUnits.symm x.1), map_one, one_mul]

theorem sourceSLocalIdeleLift_finite_in (x : SWholeUnits K S) (P : S) :
    sourceKPIdeleFiniteCoordinate K P.val (sourceSLocalIdeleLift K S x) = x.2 P := by
  rw [sourceSLocalIdeleLift_finite_product, Finset.prod_eq_single P]
  · exact sourceKPAdeleLocalUnit_same K P.val (x.2 P)
  · intro Q _ hQP
    exact sourceKPAdeleLocalUnit_other K Q.val (x.2 Q) P.val
      (fun h => hQP (Subtype.ext h.symm))
  · intro hP
    exact (hP (Finset.mem_univ P)).elim

theorem sourceSLocalIdeleLift_finite_out (x : SWholeUnits K S) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ S) :
    sourceKPIdeleFiniteCoordinate K P (sourceSLocalIdeleLift K S x) = 1 := by
  rw [sourceSLocalIdeleLift_finite_product]
  apply Finset.prod_eq_one
  intro Q _
  exact sourceKPAdeleLocalUnit_other K Q.val (x.2 Q) P (fun h => hP (h.symm ▸ Q.property))

theorem sourceSLocalIdeleLift_injective : Function.Injective (sourceSLocalIdeleLift K S) := by
  intro x y h
  apply Prod.ext
  · funext w
    simpa only [sourceSLocalIdeleLift_arch] using congrArg (sourceKPIdeleInfiniteCoordinate K w) h
  · funext P
    simpa only [sourceSLocalIdeleLift_finite_in] using congrArg (sourceKPIdeleFiniteCoordinate K P.val) h

theorem sourceSLocalIdeleLift_norm (x : SWholeUnits K S) :
    sourceKPIdeleAbsoluteNorm K (sourceSLocalIdeleLift K S x) = sLocalNorm K S x := by
  let u := sourceSLocalIdeleLift K S x
  change ‖(sourceKPIdeleInfiniteUnit K u : InfiniteAdeleRing K)‖ *
    ‖(sourceKPIdeleFiniteUnit K u : 𝔸ᶠ[K])‖ = _
  rw [InfiniteAdeleRing.norm_def, FiniteAdeleRing.norm_eq_finprod_of_unit, sLocalNorm_eq_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro w _
    change ‖(sourceKPIdeleInfiniteCoordinate K w u : w.Completion)‖ ^ w.mult = _
    rw [sourceSLocalIdeleLift_arch K S x w]
  · let f (P : HeightOneSpectrum (𝓞 K)) :=
      ‖(sourceKPIdeleFiniteCoordinate K P u : P.adicCompletion K)‖
    have hf : Function.mulSupport f ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) := by
      intro P h
      by_contra hP
      apply h
      change ‖(sourceKPIdeleFiniteCoordinate K P u : P.adicCompletion K)‖ = 1
      rw [sourceSLocalIdeleLift_finite_out K S x P hP, Units.val_one, norm_one]
    change (∏ᶠ P : HeightOneSpectrum (𝓞 K), f P) = _
    calc
      _ = ∏ P ∈ S, f P := finprod_eq_prod_of_mulSupport_subset f hf
      _ = ∏ P : S, f P.val := (Finset.prod_coe_sort S f).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro P _
        change ‖(sourceKPIdeleFiniteCoordinate K P.val u : P.val.adicCompletion K)‖ = _
        rw [sourceSLocalIdeleLift_finite_in K S x P]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

/-- The normalized projective diagonal at the actual S-local idèle. -/
def sourceSLocalProjectiveDiagonalLift (x : SWholeUnits K S) : SourceKPAdelicProjective K hζ :=
  sourceKPAdelicProjectiveDiagonalLift K hζ (sourceSLocalIdeleLift K S x)

theorem sourceSLocalProjectiveDiagonalLift_projection (x : SWholeUnits K S) :
    sourceKPAdelicProjectiveProjection K hζ (sourceSLocalProjectiveDiagonalLift K S hζ x) =
      sourceKPProjectiveDiagonalHom 𝔸[K] (sourceSLocalIdeleLift K S x) :=
  sourceKPAdelicProjectiveDiagonalLift_projection K hζ _

theorem sourceSLocalProjectiveDiagonalLift_arch (x : SWholeUnits K S) :
    (sourceSLocalProjectiveDiagonalLift K S hζ x).1 =
      sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K) (MulEquiv.piUnits.symm x.1) := by
  change sourceKPProjectiveDiagonalHom (InfiniteAdeleRing K)
    (sourceKPIdeleInfiniteUnit K (sourceSLocalIdeleLift K S x)) = _
  rw [sourceSLocalIdeleLift_infinite_unit]

end
end ArtinMatthews
