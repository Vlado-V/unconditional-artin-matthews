module

public import ArtinMatthews.SourceHyperbolicH1Tests
public import ArtinMatthews.SourceHyperbolicH1Measure
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Compact chart tests and the exact local L2 support space. -/
namespace ArtinMatthews.SourceHyperbolicGreen
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

def h1OutsideRestriction (U : Set (ProductSpace ι)) :
    H1Mass ι →L[ℝ] Lp ℂ 2 ((productVolume ι).restrict Uᶜ) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_le_self (μ := productVolume ι) (s := Uᶜ))

def h1SupportedMass (U : Set (ProductSpace ι)) : Submodule ℂ (H1Mass ι) where
  carrier := {f | ∀ᵐ p ∂productVolume ι, p ∉ U → f p = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := productVolume ι)] with p hp
    exact fun _ => hp
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf,hg,Lp.coeFn_add f g] with p hfp hgp hp
    intro hpu
    rw [hp]
    change f p + g p = 0
    rw [hfp hpu,hgp hpu,add_zero]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf,Lp.coeFn_smul c f] with p hfp hp
    intro hpu
    rw [hp]
    change c • f p = 0
    rw [hfp hpu,smul_zero]

theorem h1OutsideRestriction_eq_zero_iff (U : Set (ProductSpace ι))
    (hU : MeasurableSet U) (f : H1Mass ι) :
    h1OutsideRestriction U f = 0 ↔ f ∈ h1SupportedMass U := by
  have hco : (h1OutsideRestriction U f : ProductSpace ι → ℂ) =ᵐ[(productVolume ι).restrict Uᶜ] f :=
    Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
  constructor
  · intro hf
    have hz : ∀ᵐ p ∂(productVolume ι).restrict Uᶜ, f p = 0 := by
      filter_upwards [hco,Lp.coeFn_zero (E := ℂ) (p := 2)
        (μ := (productVolume ι).restrict Uᶜ)] with p hp hp0
      rw [hf] at hp
      exact hp.symm.trans hp0
    exact (ae_restrict_iff' hU.compl).mp hz
  · intro hf
    apply Lp.ext
    filter_upwards [hco,(ae_restrict_iff' hU.compl).mpr hf,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (productVolume ι).restrict Uᶜ)] with p hp hz hp0
    exact hp.trans (hz.trans hp0.symm)

theorem h1SupportedMass_isClosed (U : Set (ProductSpace ι)) (hU : MeasurableSet U) :
    IsClosed (h1SupportedMass U : Set (H1Mass ι)) := by
  have he : (h1SupportedMass U : Set (H1Mass ι)) = (h1OutsideRestriction U).ker := by
    ext f
    exact (h1OutsideRestriction_eq_zero_iff U hU f).symm
  rw [he]
  exact (h1OutsideRestriction U).isClosed_ker

def h1LocalTests (U : Set (ProductSpace ι)) : Submodule ℂ (h1Tests ι 2) where
  carrier := {f | tsupport (f : ProductSpace ι → ℂ) ⊆ U}
  zero_mem' := by simp
  add_mem' := fun hf hg => (tsupport_add _ _).trans (Set.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    change tsupport (fun p => c • f.val p) ⊆ U
    exact (tsupport_smul_subset_right _ _).trans hf

def h1LocalTestMass (U : Set (ProductSpace ι)) : h1LocalTests U →ₗ[ℂ] h1SupportedMass U where
  toFun f := ⟨h1TestMass f.val, by
    filter_upwards [h1TestMass_coe f.val] with p hp
    intro hpu
    rw [hp]
    exact image_eq_zero_of_notMem_tsupport fun hpt => hpu (f.prop hpt)⟩
  map_add' f g := by
    apply Subtype.ext
    exact (h1TestMassLinear ι 2).map_add f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (h1TestMassLinear ι 2).map_smul c f.val

theorem h1LocalTestMass_denseRange (U : Set (ProductSpace ι))
    (hU : IsOpen U) (hUupper : U ⊆ productUpper ι) : DenseRange (h1LocalTestMass U) := by
  let : CompleteSpace (h1SupportedMass U) := (h1SupportedMass_isClosed U hU.measurableSet).completeSpace_coe
  let R := LinearMap.range (h1LocalTestMass U)
  have horth : Rᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    have hzero : ∀ᵐ p ∂productVolume ι, p ∈ U → f.val p = 0 := by
      apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((h1_memLp_locallyIntegrableOn (Lp.memLp f.val)).mono_set hUupper)
      intro g hg hc hs
      let φ : h1LocalTests U :=
        ⟨h1RealTest g (hg.of_le (by simp)) hc (hs.trans hUupper),by
          change tsupport (fun p => (g p : ℂ)) ⊆ U
          exact (tsupport_comp_subset (g := Complex.ofReal) rfl g).trans hs⟩
      have hp := (Submodule.mem_orthogonal R f).mp hf (h1LocalTestMass U φ) ⟨φ,rfl⟩
      change inner ℂ (h1TestMass φ.val) f.val = 0 at hp
      rw [h1TestMass_inner] at hp
      simpa [φ,h1RealTest,RCLike.real_smul_eq_coe_mul] using hp
    have hz : f.val = 0 := by
      apply Lp.ext
      filter_upwards [hzero,f.prop,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := productVolume ι)] with p hi ho hp0
      by_cases hp : p ∈ U
      · exact (hi hp).trans hp0.symm
      · exact (ho hp).trans hp0.symm
    exact Subtype.ext hz
  have htop : R.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,horth,Submodule.bot_orthogonal_eq_top]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htop

end
end ArtinMatthews.SourceHyperbolicGreen
