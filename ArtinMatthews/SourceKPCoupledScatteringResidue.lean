module

public import ArtinMatthews.SourceKPCoupledTraceFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The scalar continuation and its exact residue at the actual coupled wild test. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic Filter
open scoped NumberField AdeleRing Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "arch" => (fun s : ℂ => ((Real.pi : ℂ)/s)^Fintype.card (InfinitePlace K))

def sourceKPCoupledScatteringContinuation (S : Finset Places) (s : ℂ) : ℂ :=
  arch s * (sourceKPExteriorScattering S s * sourceKPCoupledWindowContinuation K S s)

def sourceKPCoupledScatteringResidue (S : Finset Places) : ℂ :=
  arch (1/6) * (sourceKPExteriorScatteringResidue S * sourceKPCoupledWindowContinuation K S (1/6))

private theorem sourceKPCoupledScattering_arch_analyticAt {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ arch s := by
  have hs0 : s ≠ 0 := fun h => by rw [h,Complex.zero_re] at hs; exact (lt_irrefl _ hs)
  have ha : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ)/z) s :=
    analyticAt_const.div analyticAt_id hs0
  exact ha.pow _

theorem sourceKPCoupledScatteringContinuation_meromorphic (S : Finset Places) :
    MeromorphicOn (sourceKPCoupledScatteringContinuation K S) {s | 0 < s.re} := by
  intro s hs
  exact (sourceKPCoupledScattering_arch_analyticAt K hs).meromorphicAt.mul
    ((sourceKPExteriorScattering_meromorphic S s).mul
      (sourceKPCoupledWindowContinuation_analyticAt K S hs).meromorphicAt)

theorem sourceKPCoupledScatteringResidue_ne_zero (S : Finset Places) :
    sourceKPCoupledScatteringResidue K S ≠ 0 := by
  unfold sourceKPCoupledScatteringResidue
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by norm_num)))
    (mul_ne_zero (sourceKPExteriorScatteringResidue_ne_zero S)
      (sourceKPCoupledWindowContinuation_ne_zero K S))

theorem sourceKPCoupledScatteringResidue_tendsto (S : Finset Places) :
    Tendsto (fun s => (s-1/6)*sourceKPCoupledScatteringContinuation K S s)
      (𝓝[≠] (1/6 : ℂ)) (𝓝 (sourceKPCoupledScatteringResidue K S)) := by
  have ha : Tendsto arch (𝓝[≠] (1/6 : ℂ)) (𝓝 (arch (1/6))) :=
    (sourceKPCoupledScattering_arch_analyticAt K (s := 1/6) (by norm_num)).continuousAt.mono_left
      nhdsWithin_le_nhds
  have hw : Tendsto (sourceKPCoupledWindowContinuation K S) (𝓝[≠] (1/6 : ℂ))
      (𝓝 (sourceKPCoupledWindowContinuation K S (1/6))) :=
    (sourceKPCoupledWindowContinuation_analyticAt K S (s := 1/6) (by norm_num)).continuousAt.mono_left
      nhdsWithin_le_nhds
  refine (ha.mul ((sourceKPExteriorScattering_residue S).mul hw)).congr' ?_
  exact Eventually.of_forall fun s => by
    unfold sourceKPCoupledScatteringContinuation
    ring

theorem sourceKPCoupledScatteringContinuation_initial :
    ∃ S : Finset Places,
      sixthWildPrimes K ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      ∀ s : ℂ, ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        sourceKPAdelicTraceIntertwiner K hζ s (1,(sourceKPCoupledWildWeyl K hζ).2) =
          sourceKPCoupledScatteringContinuation K S s := by
  obtain ⟨S,hW,hH,hB,h⟩ := sourceKPCoupledTraceIntertwiner_eq_window K hζ
  refine ⟨S,hW,hH,hB,fun s hs => ?_⟩
  rw [show (1,(sourceKPCoupledWildWeyl K hζ).2) = sourceKPCoupledWildWeyl K hζ from
    Prod.ext (sourceKPCoupledWildWeyl_arch K hζ).symm rfl]
  exact h s hs

end
end ArtinMatthews
