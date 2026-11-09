module

public import ArtinMatthews.SourceKPAdelicOutgoingTraceCoordinate
public import ArtinMatthews.SourceFiniteFiberScattering
public import Mathlib.Analysis.Analytic.Uniqueness


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite-window regularization is analytic on the whole
positive half-plane. The full archimedean spherical product is entire,
and initial identities propagate on this connected domain. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourceArchJacquet Matrix Filter
open scoped NumberField MatrixGroups AdeleRing Topology BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]

abbrev SourceKPAdelicOutgoingInitial (s : ℂ) : Prop :=
  ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1

theorem sourceKPAdelicOutgoingInitial_re_one_le {s : ℂ}
    (hs : SourceKPAdelicOutgoingInitial K s) : 1 ≤ s.re := by
  have hn : (3 : ℕ) ≤ 3*(Module.finrank ℚ K+1) := by omega
  have hr : (3 : ℝ) ≤ ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) := by exact_mod_cast hn
  change ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1 at hs
  linarith

theorem sourceKPAdelicOutgoingInitial_ne_exceptional {s : ℂ}
    (hs : SourceKPAdelicOutgoingInitial K s) : s ≠ (1/6 : ℂ) := by
  intro h
  have h₁ := sourceKPAdelicOutgoingInitial_re_one_le K hs
  rw [h] at h₁
  norm_num at h₁

theorem sourceKPAdelicOutgoingAnalytic_eqOn_of_initial {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {s : ℂ | 0 < s.re})
    (hg : AnalyticOnNhd ℂ g {s : ℂ | 0 < s.re})
    (he : ∀ s, SourceKPAdelicOutgoingInitial K s → f s = g s) :
    Set.EqOn f g {s : ℂ | 0 < s.re} := by
  let n : ℝ := ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ)
  let c : ℂ := (n+1 : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hc : c ∈ {s : ℂ | 0 < s.re} := by
    change 0 < c.re
    rw [show c.re = n+1 from Complex.ofReal_re _]
    linarith
  have hc' : c ∈ {s : ℂ | n < s.re} := by
    change n < c.re
    rw [show c.re = n+1 from Complex.ofReal_re _]
    linarith
  have hlocal : f =ᶠ[𝓝 c] g := by
    filter_upwards [(Complex.isOpen_re_gt n).mem_nhds hc'] with z hz
    apply he z
    change n ≤ 2*z.re+1
    change n < z.re at hz
    linarith
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpre hc hlocal

theorem sourceKPAdelicOutgoingArchSection_analyticAt (g : PGL(2, ℂ)) (s : ℂ) :
    AnalyticAt ℂ (fun z => sourceArchSphericalSection (-z) g) s := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    have hp : (sourceArchHeight g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceArchHeight_pos g).ne'
    have ha : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ)*(-z)+1) s :=
      (analyticAt_const.mul analyticAt_id.neg).add analyticAt_const
    simp_rw [sourceArchSphericalSection_mk,sourceArchSphericalGL,Complex.cpow_def_of_ne_zero hp]
    exact (analyticAt_const.mul ha).cexp'

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicOutgoingArchProduct_analyticAt (g : PGL(2, InfiniteAdeleRing K)) (s : ℂ) :
    AnalyticAt ℂ (fun z => sourceArchSphericalProduct K hζ (-z) g) s := by
  unfold sourceArchSphericalProduct
  exact Finset.analyticAt_fun_prod _ (fun v _ =>
    sourceKPAdelicOutgoingArchSection_analyticAt (sourceArchProjectiveAt K hζ v g) s)

theorem sourceKPAdelicOutgoingFiniteRegularized_analyticAt
    (g : SourceKPFiniteAdeleProjective K hζ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (sourceKPFiniteFiberScatteringRegularized K hζ g S) s := by
  by_cases h : s = (1/6 : ℂ)
  · subst s
    exact sourceKPFiniteFiberScatteringRegularized_analyticAt K hζ g S
  · have ha : AnalyticAt ℂ (fun z : ℂ => z-1/6) s := analyticAt_id.sub analyticAt_const
    refine (ha.mul (sourceKPFiniteFiberScatteringContinuation_analyticAt K hζ g S hs h)).congr ?_
    filter_upwards [eventually_ne_nhds h] with z hz
    exact (sourceKPFiniteFiberScatteringRegularized_eq K hζ g S hz).symm

end
end ArtinMatthews
