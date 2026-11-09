module

public import ArtinMatthews.SourceFiniteWindowHolomorphic
public import ArtinMatthews.SourceAdelicIntertwinerEuler
public import ArtinMatthews.SourceKPExteriorScattering


set_option backward.privateInPublic true
@[expose] public section

/-! Meromorphic continuation at every actual finite fibre, retaining the
literal coupled window in the residue. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain StandardAdelic SourceArchJacquet Filter
open scoped NumberField AdeleRing Topology BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Places" => HeightOneSpectrum (𝓞 K)
local notation "arch" => (fun s : ℂ => ((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K))

def sourceKPFiniteFiberScatteringContinuation (g : SourceKPFiniteAdeleProjective K hζ)
    (S : Finset Places) (s : ℂ) : ℂ :=
  arch s * (sourceKPExteriorScattering S s *
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g) S)

def sourceKPFiniteFiberScatteringRegularized (g : SourceKPFiniteAdeleProjective K hζ)
    (S : Finset Places) (s : ℂ) : ℂ :=
  arch s * (sourceKPExteriorScatteringRegularized S s *
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ s g) S)

def sourceKPFiniteFiberScatteringResidue (g : SourceKPFiniteAdeleProjective K hζ)
    (S : Finset Places) : ℂ :=
  arch (1 / 6) * (sourceKPExteriorScatteringResidue S *
    sourceKPFiniteWindowIntegral K (sourceKPFiniteIntertwiningKernel K hζ (1 / 6) g) S)

private theorem finiteFiberScattering_arch_analyticAt {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ arch s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact (lt_irrefl _ hs)
  have ha : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) / z) s :=
    analyticAt_const.div analyticAt_id hs0
  exact ha.pow _

theorem sourceKPFiniteFiberScatteringContinuation_meromorphicOn
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset Places) :
    MeromorphicOn (sourceKPFiniteFiberScatteringContinuation K hζ g S) {s | 0 < s.re} := by
  intro s hs
  exact (finiteFiberScattering_arch_analyticAt K hs).meromorphicAt.mul
    ((sourceKPExteriorScattering_meromorphic S s).mul
      (sourceKPFiniteWindowIntertwiner_analyticOnNhd K hζ g S s hs).meromorphicAt)

theorem sourceKPFiniteFiberScatteringContinuation_analyticAt
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset Places)
    {s : ℂ} (hs : 0 < s.re) (hs₀ : s ≠ 1 / 6) :
    AnalyticAt ℂ (sourceKPFiniteFiberScatteringContinuation K hζ g S) s := by
  have h₁ : AnalyticAt ℂ (fun z : ℂ => 6 * z) s := analyticAt_const.mul analyticAt_id
  have h₂ : AnalyticAt ℂ (fun z : ℂ => 6 * z + 1) s := h₁.add analyticAt_const
  have hn : 6 * s ≠ (1 : ℂ) := by
    intro he
    apply hs₀
    linear_combination (1 / 6 : ℂ) * he
  have hd : 1 < (6 * s + 1).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hd' : 6 * s + 1 ≠ (1 : ℂ) := by
    intro he
    rw [he, Complex.one_re] at hd
    exact (lt_irrefl _ hd)
  have hE : AnalyticAt ℂ (sourceKPExteriorScattering S) s :=
    ((sourceKPExteriorZeta_analyticAt S hn).comp (f := fun z : ℂ => 6 * z) h₁).div
      ((sourceKPExteriorZeta_analyticAt S hd').comp (f := fun z : ℂ => 6 * z + 1) h₂)
        (sourceKPExteriorZeta_ne_zero S hd)
  exact (finiteFiberScattering_arch_analyticAt K hs).mul
    (hE.mul (sourceKPFiniteWindowIntertwiner_analyticOnNhd K hζ g S s hs))

theorem sourceKPFiniteFiberScatteringRegularized_analyticAt
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset Places) :
    AnalyticAt ℂ (sourceKPFiniteFiberScatteringRegularized K hζ g S) (1 / 6) :=
  (finiteFiberScattering_arch_analyticAt K (by norm_num : 0 < (1 / 6 : ℂ).re)).mul
    ((sourceKPExteriorScatteringRegularized_analyticAt S).mul
      (sourceKPFiniteWindowIntertwiner_analyticOnNhd K hζ g S (1 / 6) (by norm_num)))

theorem sourceKPFiniteFiberScatteringRegularized_value
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset Places) :
    sourceKPFiniteFiberScatteringRegularized K hζ g S (1 / 6) =
      sourceKPFiniteFiberScatteringResidue K hζ g S := by
  unfold sourceKPFiniteFiberScatteringRegularized sourceKPFiniteFiberScatteringResidue
  rw [sourceKPExteriorScatteringRegularized_value]

theorem sourceKPFiniteFiberScatteringRegularized_eq
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset Places)
    {s : ℂ} (hs : s ≠ 1 / 6) :
    sourceKPFiniteFiberScatteringRegularized K hζ g S s =
      (s - 1 / 6) * sourceKPFiniteFiberScatteringContinuation K hζ g S s := by
  unfold sourceKPFiniteFiberScatteringRegularized sourceKPFiniteFiberScatteringContinuation
  rw [sourceKPExteriorScatteringRegularized_eq S hs]
  ring

theorem sourceKPFiniteFiberScatteringResidue_tendsto
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset Places) :
    Tendsto (fun s => (s - 1 / 6) * sourceKPFiniteFiberScatteringContinuation K hζ g S s)
      (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (sourceKPFiniteFiberScatteringResidue K hζ g S)) := by
  have h := (sourceKPFiniteFiberScatteringRegularized_analyticAt K hζ g S).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (1 / 6 : ℂ) ≤ 𝓝 (1 / 6 : ℂ) from nhdsWithin_le_nhds)
  rw [sourceKPFiniteFiberScatteringRegularized_value] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact sourceKPFiniteFiberScatteringRegularized_eq K hζ g S (by simpa using hs)

private theorem finiteFiberScattering_archSection_one (s : ℂ) :
    sourceArchSphericalProduct K hζ s 1 = 1 := by
  unfold sourceArchSphericalProduct
  apply Finset.prod_eq_one
  intro v _
  rw [map_one, sourceArchSphericalSection_one]

theorem sourceKPFiniteFiberScatteringContinuation_exists
    (g : SourceKPFiniteAdeleProjective K hζ) (S₀ : Finset Places) :
    ∃ S : Finset Places,
      S₀ ⊆ S ∧ sourceHilbertSet K ∅ ⊆ S ∧ traceBadPlaces K ⊆ S ∧
      (∀ s : ℂ, ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1 →
        sourceKPAdelicTraceIntertwiner K hζ s (1, g) =
          sourceKPFiniteFiberScatteringContinuation K hζ g S s) ∧
      MeromorphicOn (sourceKPFiniteFiberScatteringContinuation K hζ g S) {s | 0 < s.re} ∧
      Tendsto (fun s => (s - 1 / 6) * sourceKPFiniteFiberScatteringContinuation K hζ g S s)
        (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (sourceKPFiniteFiberScatteringResidue K hζ g S)) := by
  obtain ⟨S, hS, hH, hB, hEuler⟩ := sourceKPAdelicTraceIntertwiner_eq_euler K hζ (1, g) S₀
  refine ⟨S, hS, hH, hB, ?_, sourceKPFiniteFiberScatteringContinuation_meromorphicOn K hζ g S,
    sourceKPFiniteFiberScatteringResidue_tendsto K hζ g S⟩
  intro s hs
  simpa only [Prod.fst, Prod.snd, finiteFiberScattering_archSection_one K hζ, mul_one,
    sourceKPFiniteFiberScatteringContinuation] using hEuler s hs

end
end ArtinMatthews
