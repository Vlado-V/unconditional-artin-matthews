module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedJacquetBasis
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedSlice
public import ArtinMatthews.SourceKPResidualLocalFourierFunctional


set_option backward.privateInPublic true
@[expose] public section

/-! A slice of the literal unit-frequency residue factors through
the actual local stable Jacquet values. The exterior coefficient and
the other retained translates stay in the same finite cover product. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (places : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ places
local notation "G₀" => (fun Q : ↥places => SourceFiniteKP2Projective K hζ (Subtype.val Q))
local notation "L" => sourceKPLocalCompactProductLift K hζ places
local notation "base" => sourceKPAdelicLocalBase K hζ
local notation "rest" => sourceKPAdelicOutgoingRetainedSliceRest K hζ places
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)

def sourceKPAdelicOutgoingRetainedResidualCoefficient {T : ℝ} (hT : 2 < T)
    (qf : Gf) (g : Gₛ) : ℂ :=
  C₁ (one_le_two.trans hT.le) (qf * (L g).2)

local notation "A" => sourceKPAdelicOutgoingRetainedResidualCoefficient K hζ places

variable (hs : 0 < (1 / 6 : ℂ).re)

local notation "s₀" => (1 / 6 : ℂ)
local notation "v" => (fun Q : ↥places =>
  sourceKPAdelicOutgoingRetainedJacquetVector K hζ (Subtype.val Q) hs)
local notation "W" => (fun Q : ↥places =>
  sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ
    (Singleton.singleton (Subtype.val Q) : Finset (HeightOneSpectrum (𝓞 K))) s₀ hs)

local instance sourceKPAdelicOutgoingRetainedResidualSliceAddCommGroup (P : ↥places) :
    AddCommGroup (W P) := Submodule.addCommGroup _

theorem sourceKPAdelicOutgoingRetainedResidualCoefficient_slice_linear {T : ℝ} (hT : 2 < T)
    (qf : Gf) (g : Gₛ) (P : ↥places) (hqf : base P.val (1,qf) = 1) :
    ∃ B : W P →ₗ[ℂ] ℂ, ∀ x : G₀ P, A hT qf (Function.update g P x) = B (v P x) := by
  let r := rest qf g P
  have hr := sourceKPAdelicOutgoingRetainedSliceRest_base_one K hζ places qf g P hqf
  let ℓ := sourceKPResidualLocalFourierFunctional K hζ P.val hs hT r
  obtain ⟨B,hB⟩ := sourceKPAdelicOutgoingRegularizedLocalJacquetMap_whittaker_factors K hζ P.val s₀ hs ℓ
    (sourceKPResidualLocalFourierFunctional_upper K hζ P.val hs hT r hr)
  refine ⟨B,fun x => ?_⟩
  let f := sourceKPJacquetRight K hζ P.val
    (sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P.val s₀ hs)
    (sourceKPAdelicOutgoingRegularizedLocalCyclic K hζ P.val s₀ hs)
    (sourceKPAdelicOutgoingRegularizedLocalCyclic_invariant K hζ P.val s₀ hs) x
    (sourceKPAdelicOutgoingRegularizedLocalCyclicVector K hζ P.val s₀ hs)
  calc
    A hT qf (Function.update g P x) =
        C₁ (one_le_two.trans hT.le) (r * (sourceKPAdelicLocalProjective K hζ P.val x).2) :=
      congrArg (C₁ (one_le_two.trans hT.le))
        (sourceKPAdelicOutgoingRetainedSliceRest_mul_local K hζ places qf g P x)
    _ = ℓ f := (sourceKPResidualLocalFourierFunctional_generator K hζ P.val hs hT r x).symm
    _ = B (v P x) := (hB f).symm

theorem sourceKPAdelicOutgoingRetainedResidualCoefficient_slice_relation {T : ℝ} (hT : 2 < T)
    (qf : Gf) (g : Gₛ) (P : ↥places) (hqf : base P.val (1,qf) = 1)
    (d : G₀ P →₀ ℂ) (hd : d.sum (fun x z => z • v P x) = 0) :
    d.sum (fun x z => z * A hT qf (Function.update g P x)) = 0 := by
  obtain ⟨B,hB⟩ := sourceKPAdelicOutgoingRetainedResidualCoefficient_slice_linear K hζ places hs hT qf g P hqf
  have he : B (d.sum (fun x z => z • v P x)) =
      d.sum (fun x z => z * A hT qf (Function.update g P x)) := by
    simp only [Finsupp.sum,map_sum,map_smul,smul_eq_mul,hB]
  exact he.symm.trans ((congrArg (⇑B) hd).trans (map_zero B))

end
end ArtinMatthews
