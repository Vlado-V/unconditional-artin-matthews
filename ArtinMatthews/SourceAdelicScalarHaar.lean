module

public import ArtinMatthews.SourceAdelicTraceHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Dynamics.Ergodic.Action.Regular


set_option backward.privateInPublic true
@[expose] public section

/-! Principal field scalars preserve the actual normalized additive adelic Haar measure. -/
namespace ArtinMatthews
open NumberField MeasureTheory MeasureTheory.Measure
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local instance sourceKPScalarHaarAdelicMeasurable : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance sourceKPScalarHaarAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceKPScalarHaarAdelicSecondCountable : SecondCountableTopology 𝔸[K] :=
  (CompactQuotient.Construction.adelicMixedHomeomorph K).secondCountableTopology

def sourceKPAdelicPrincipalMul (a : Kˣ) : 𝔸[K] ≃ₜ+ 𝔸[K] where
  toFun y := algebraMap K 𝔸[K] (a : K) * y
  invFun y := algebraMap K 𝔸[K] ((a⁻¹ : Kˣ) : K) * y
  left_inv y := by simp [← mul_assoc, ← map_mul]
  right_inv y := by simp [← mul_assoc, ← map_mul]
  map_add' x y := mul_add _ x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

lemma sourceKPAdelicPrincipalMul_apply (a : Kˣ) (y : 𝔸[K]) :
    sourceKPAdelicPrincipalMul K a y = algebraMap K 𝔸[K] (a : K) * y := rfl

lemma sourceKPAdelicPrincipalMul_measurableEmbedding (a : Kˣ) :
    MeasurableEmbedding (sourceKPAdelicPrincipalMul K a) :=
  (sourceKPAdelicPrincipalMul K a).toHomeomorph.measurableEmbedding

lemma sourceKPAdelicPrincipalMul_rational (a : Kˣ) (q : K) :
    sourceKPAdelicPrincipalMul K a (algebraMap K 𝔸[K] q) =
      algebraMap K 𝔸[K] ((a : K) * q) := by
  rw [sourceKPAdelicPrincipalMul_apply, map_mul]

lemma sourceKPAdelicPrincipalMul_map_isHaar (a : Kˣ) :
    (Measure.map (sourceKPAdelicPrincipalMul K a) (sourceKPAdelicStandardHaar K)).IsAddHaarMeasure :=
  (sourceKPAdelicPrincipalMul K a).isAddHaarMeasure_map (sourceKPAdelicStandardHaar K)

theorem sourceKPAdelicStandardHaar_principal_mul (a : Kˣ) :
    MeasurePreserving (fun y : 𝔸[K] => algebraMap K 𝔸[K] (a : K) * y)
      (sourceKPAdelicStandardHaar K) (sourceKPAdelicStandardHaar K) := by
  let f := sourceKPAdelicPrincipalMul K a
  have hf : Measurable (f : 𝔸[K] → 𝔸[K]) := f.continuous.measurable
  let μ := sourceKPAdelicStandardHaar K
  let ν := Measure.map f μ
  let : ν.IsAddHaarMeasure := sourceKPAdelicPrincipalMul_map_isHaar K a
  let c := Measure.addHaarScalarFactor ν μ
  have hscale : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hqmp : QuasiMeasurePreserving f μ μ := by
    refine ⟨hf, ?_⟩
    change ν ≪ μ
    rw [hscale]
    exact smul_absolutelyContinuous
  let R := sourceKPRationalAdeleEquiv K
  let e : Equiv.Perm (sourceKPAdelicRationals K) :=
    (R.symm.toEquiv.trans (a⁻¹).mulLeft).trans R.toEquiv
  have he (q : K) : e (R q) = R (((a⁻¹ : Kˣ) : K) * q) := by
    change R ((a⁻¹).mulLeft (R.symm (R q))) = _
    rw [AddEquiv.symm_apply_apply]
    rfl
  have hcomm (g : sourceKPAdelicRationals K) (x : 𝔸[K]) :
      f ((e g : 𝔸[K]) + x) = (g : 𝔸[K]) + f x := by
    obtain ⟨q, rfl⟩ := R.surjective g
    rw [he]
    change f (algebraMap K 𝔸[K] (((a⁻¹ : Kˣ) : K) * q) + x) =
      algebraMap K 𝔸[K] q + f x
    rw [map_add, sourceKPAdelicPrincipalMul_rational]
    simp
  have hfd : IsAddFundamentalDomain (sourceKPAdelicRationals K)
      (f ⁻¹' sourceKPAdelicFundamentalDomain K) μ :=
    (sourceKPAdelicFundamentalDomain_isFundamental K μ).preimage_of_equiv
      hqmp e.bijective hcomm
  have hν : ν (sourceKPAdelicFundamentalDomain K) = 1 := by
    change (Measure.map f μ) (sourceKPAdelicFundamentalDomain K) = 1
    rw [Measure.map_apply hf (sourceKPAdelicFundamentalDomain_measurable K)]
    exact (hfd.measure_eq (sourceKPAdelicFundamentalDomain_isFundamental K μ)).trans
      (sourceKPAdelicStandardHaar_fundamentalDomain K)
  have hc : (c : ℝ≥0∞) = 1 := by
    have hh := congrArg (fun m : Measure 𝔸[K] => m (sourceKPAdelicFundamentalDomain K)) hscale
    simpa only [hν, Measure.coe_nnreal_smul_apply, μ,
      sourceKPAdelicStandardHaar_fundamentalDomain, mul_one] using hh.symm
  have hc' : c = 1 := ENNReal.coe_injective hc
  refine ⟨hf, ?_⟩
  calc
    Measure.map (fun y : 𝔸[K] => algebraMap K 𝔸[K] (a : K) * y) μ = ν := rfl
    _ = μ := by simpa only [hc', one_smul] using hscale

end
end ArtinMatthews
