module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuationSection
public import ArtinMatthews.SourceKPCoupledTraceFactor


set_option backward.privateInPublic true
@[expose] public section

/-! At the actual pole the full outgoing section has exactly the
scattering residue at coordinate one. Every relation in its genuine
translated section therefore gives the corresponding scalar relation
at every finite remainder. The actual wild test supplies nonvanishing. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourceArchJacquet Matrix
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "G" => SourceKPAdelicProjective K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "H" => SourceKPAdelicOutgoingInitial K
local notation "I" => sourceKPAdelicTraceIntertwiner K hζ
local notation "C" => sourceKPFiniteFiberScatteringContinuation K hζ
local notation "R" => sourceKPFiniteFiberScatteringResidue K hζ
local notation "E" => sourceKPAdelicOutgoingExceptionalSection K hζ
local notation "Π₋" => SourceKPAdelicPrincipalSeries K hζ (-(1/6 : ℂ))
local notation "ρ₋" => sourceKPAdelicPrincipalSeriesRepresentation K hζ (-(1/6 : ℂ))

theorem sourceKPAdelicOutgoingExceptionalSection_scattering_one (qf : Gf) (S : Finset Pr)
    (hS : ∀ s, H s → I s (1,qf) = C qf S s) :
    ((E).val (1,qf)).val 1 = R qf S := by
  change sourceKPAdelicOutgoingRegularizedCoordinate K hζ (1/6) (1,qf) 1 = _
  rw [sourceKPAdelicOutgoingRegularizedCoordinate_one K hζ,
    sourceKPAdelicOutgoingRegularizedScalar_residue K hζ (1,qf) S hS]
  have ha : sourceArchSphericalProduct K hζ (-(1/6 : ℂ)) 1 = 1 := by
    simp only [sourceArchSphericalProduct,map_one,sourceArchSphericalSection_one,Finset.prod_const_one]
  change sourceArchSphericalProduct K hζ (-(1/6 : ℂ)) 1 * R qf S = _
  rw [ha,one_mul]

theorem sourceKPAdelicOutgoingExceptionalSection_scattering_relation
    {A : Type*} [Fintype A] (t : A → Gf) (c : A → ℂ)
    (hrel : ∑ i, c i • ρ₋ (1,t i) E = 0)
    (qf : Gf) (S : A → Finset Pr)
    (hS : ∀ i s, H s → I s (1,qf*t i) = C (qf*t i) (S i) s) :
    ∑ i, c i * R (qf*t i) (S i) = 0 := by
  let e : Π₋ →ₗ[ℂ] ℂ :=
    { toFun := fun f => (f.val (1,qf)).val 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he (i : A) : e (ρ₋ (1,t i) E) = R (qf*t i) (S i) := by
    change ((E).val (((1,qf) : G)*(1,t i))).val 1 = _
    have hp : ((1,qf) : G)*(1,t i) = (1,qf*t i) := by
      apply Prod.ext
      · exact one_mul _
      · rfl
    rw [hp]
    exact sourceKPAdelicOutgoingExceptionalSection_scattering_one K hζ (qf*t i) (S i) (hS i)
  simpa only [map_sum,map_smul,smul_eq_mul,map_zero,he] using congrArg e hrel

theorem sourceKPAdelicOutgoingExceptionalSection_canonical_scattering_relation
    {A : Type*} [Fintype A] (t : A → Gf) (c : A → ℂ)
    (hrel : ∑ i, c i • ρ₋ (1,t i) E = 0) (qf : Gf) :
    ∑ i, c i * R (qf*t i) (sourceKPAdelicOutgoingScatteringWindow K hζ (qf*t i)) = 0 :=
  sourceKPAdelicOutgoingExceptionalSection_scattering_relation K hζ t c hrel qf
    (fun i => sourceKPAdelicOutgoingScatteringWindow K hζ (qf*t i))
    (fun i s hs => sourceKPAdelicOutgoingScatteringWindow_matches K hζ (qf*t i) s hs)

theorem sourceKPAdelicOutgoingExceptionalSection_wild_ne_zero :
    ((E).val (sourceKPCoupledWildWeyl K hζ)).val 1 ≠ 0 := by
  let qf := (sourceKPCoupledWildWeyl K hζ).2
  have hg : ((1,qf) : G) = sourceKPCoupledWildWeyl K hζ :=
    Prod.ext (sourceKPCoupledWildWeyl_arch K hζ).symm rfl
  obtain ⟨S,_,_,_,hM⟩ := sourceKPCoupledTraceIntertwiner_eq_window K hζ
  have hS (s : ℂ) (hs : H s) : I s (1,qf) = C qf S s := by
    rw [hg,hM s hs,sourceKPFiniteFiberScatteringContinuation]
    change _ = ((Real.pi : ℂ)/s)^Fintype.card (InfinitePlace K) *
      (sourceKPExteriorScattering S s * sourceKPFiniteWindowIntegral K
        (sourceKPFiniteIntertwiningKernel K hζ s (sourceKPCoupledWildWeyl K hζ).2) S)
    rw [sourceKPCoupledWindowContinuation_agrees K hζ S hs]
  have hw : sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ (1/6) qf) S =
      sourceKPCoupledWindowContinuation K S (1/6) := by
    apply sourceKPAdelicOutgoingAnalytic_eqOn_of_initial K
      (fun s hs => sourceKPFiniteWindowIntertwiner_analyticOnNhd K hζ qf S s hs)
      (fun s hs => sourceKPCoupledWindowContinuation_analyticAt K S (s:=s) hs)
      (fun s hs => sourceKPCoupledWindowContinuation_agrees K hζ S hs)
    norm_num
  rw [← hg,sourceKPAdelicOutgoingExceptionalSection_scattering_one K hζ qf S hS,
    sourceKPFiniteFiberScatteringResidue,hw]
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (by norm_num)))
    (mul_ne_zero (sourceKPExteriorScatteringResidue_ne_zero S)
      (sourceKPCoupledWindowContinuation_ne_zero K S))

theorem sourceKPAdelicOutgoingExceptionalSection_ne_zero : E ≠ 0 := by
  intro h
  apply sourceKPAdelicOutgoingExceptionalSection_wild_ne_zero K hζ
  rw [h]
  rfl

end
end ArtinMatthews
