module

public import ArtinMatthews.SourceKPFiniteUnitTopology
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Comparison of the CFT idele model with the actual units of the adele ring. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology
open scoped NumberField AdeleRing BigOperators NNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPCFTIdeleEquiv : _root_.IdeleGroup K ≃* NumberField.IdeleGroup (𝓞 K) K :=
  _root_.IdeleGroup.equivAdeleRingUnits

lemma sourceKPCFTFiniteEquiv_continuous :
    Continuous (_root_.IdeleGroup.finiteEquivFiniteAdeleUnits (K := K)) := by
  change Continuous (_root_.IdeleGroup.finiteEquivFiniteAdeleUnits (K := K)).toMonoidHom
  apply Continuous.of_coeHom_comp
  let hval : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Set.MapsTo (Units.val : (P.adicCompletion K)ˣ → P.adicCompletion K)
        ((P.adicCompletionIntegers K).units : Set (P.adicCompletion K)ˣ)
        (P.adicCompletionIntegers K : Set (P.adicCompletion K)) :=
    Filter.Eventually.of_forall (fun _ _ hu => hu.1)
  change Continuous (RestrictedProduct.map (fun P : HeightOneSpectrum (𝓞 K) => (Units.val : (P.adicCompletion K)ˣ → P.adicCompletion K)) hval)
  exact RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id _ hval
    (fun _ => Units.continuous_val)

lemma sourceKPCFTIdeleEquiv_continuous : Continuous (sourceKPCFTIdeleEquiv K) := by
  exact Homeomorph.prodUnits.symm.continuous.comp
    (continuous_fst.prodMk (sourceKPCFTFiniteEquiv_continuous K |>.comp continuous_snd))

lemma sourceKPCFTIdeleEquiv_principal (q : Kˣ) :
    sourceKPCFTIdeleEquiv K (_root_.IdeleGroup.principalIdele K q) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 K) K q := by
  exact (_root_.IdeleGroup.equivAdeleRingUnits (K := K)).apply_symm_apply _

lemma sourceKPCFTLocalNorm (P : HeightOneSpectrum (𝓞 K)) (x : (P.adicCompletion K)ˣ) :
    ‖(x : P.adicCompletion K)‖ =
      ((P.asIdeal.absNorm : ℝ) ^ (_root_.FiniteIdeleGroup.localOrder P x).toAdd)⁻¹ := by
  have hx : (Valued.v (x : P.adicCompletion K) : WithZero (Multiplicative ℤ)) ≠ 0 := by simp
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero P) hx]
  simp only [NNReal.coe_zpow, NNReal.coe_natCast, _root_.FiniteIdeleGroup.localOrder_apply,
    zpow_neg, inv_inv]

lemma sourceKPCFTFiniteNorm_real (a : _root_.FiniteIdeleGroup K) :
    (((_root_.FiniteIdeleGroup.absoluteNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      ∏ᶠ P : HeightOneSpectrum (𝓞 K),
        (P.asIdeal.absNorm : ℝ) ^ (_root_.FiniteIdeleGroup.localOrder P (a P)).toAdd := by
  classical
  let e := (_root_.FiniteIdeleGroup.valuationVector a).toAdd
  have hs : Function.mulSupport (fun P => (P.asIdeal.absNorm : ℝ) ^ e P) ⊆ e.support := by
    intro P hP
    by_contra hp
    apply hP
    change (P.asIdeal.absNorm : ℝ) ^ e P = 1
    rw [Finsupp.notMem_support_iff.mp hp, zpow_zero]
  have he (P : HeightOneSpectrum (𝓞 K)) : e P = (_root_.FiniteIdeleGroup.localOrder P (a P)).toAdd := rfl
  simp_rw [← he]
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  change (((∏ P ∈ e.support, _root_.FiniteIdeleGroup.primeNorm P ^ e P : ℝ≥0ˣ) : ℝ≥0) : ℝ) = _
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, NNReal.coe_prod, NNReal.coe_zpow,
    _root_.FiniteIdeleGroup.primeNorm, Units.val_mk0, NNReal.coe_natCast]

lemma sourceKPCFTFiniteNorm_inv (a : _root_.FiniteIdeleGroup K) :
    ‖(_root_.IdeleGroup.finiteEquivFiniteAdeleUnits a : 𝔸ᶠ[K])‖ =
      (((_root_.FiniteIdeleGroup.absoluteNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ)⁻¹ := by
  rw [FiniteAdeleRing.norm_eq_finprod_of_unit]
  calc
    _ = ∏ᶠ P : HeightOneSpectrum (𝓞 K),
        ((P.asIdeal.absNorm : ℝ) ^ (_root_.FiniteIdeleGroup.localOrder P (a P)).toAdd)⁻¹ := by
      apply finprod_congr
      intro P
      exact sourceKPCFTLocalNorm K P (a P)
    _ = (∏ᶠ P : HeightOneSpectrum (𝓞 K),
        (P.asIdeal.absNorm : ℝ) ^ (_root_.FiniteIdeleGroup.localOrder P (a P)).toAdd)⁻¹ :=
      finprod_inv_distrib _
    _ = _ := by rw [sourceKPCFTFiniteNorm_real K a]

lemma sourceKPCFTArchNorm_real (a : _root_.InfiniteIdeleGroup K) :
    (((_root_.InfiniteIdeleGroup.archimedeanNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      ‖(a : InfiniteAdeleRing K)‖ := by
  rw [InfiniteAdeleRing.norm_def, _root_.InfiniteIdeleGroup.archimedeanNorm_apply]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val, NNReal.coe_prod, NNReal.coe_pow,
    nnnormUnitHom_val, coe_nnnorm]
  rfl

lemma sourceKPCFTIdeleEquiv_norm (a : _root_.IdeleGroup K) :
    sourceKPIdeleAbsoluteNorm K (sourceKPCFTIdeleEquiv K a) =
      (((_root_.IdeleGroup.absoluteNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ)⁻¹ := by
  change ‖(a.1 : InfiniteAdeleRing K)‖ *
    ‖(_root_.IdeleGroup.finiteEquivFiniteAdeleUnits a.2 : 𝔸ᶠ[K])‖ = _
  rw [sourceKPCFTFiniteNorm_inv, ← sourceKPCFTArchNorm_real]
  simp only [_root_.IdeleGroup.absoluteNorm_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    NNReal.coe_mul, NNReal.coe_inv, mul_inv_rev, inv_inv]

end
end ArtinMatthews
