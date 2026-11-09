module

public import ArtinMatthews.SourceKPAutomorphicExhaustion
public import ArtinMatthews.SourceKPAdelicScalarCutoff
public import ArtinMatthews.SourceKPCompactEisensteinChart
public import ArtinMatthews.SourceKPCompactC2Core


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix SourceArchJacquet SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicExhaustionCutoff_upper (n : ℕ)
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (p : ProductSpace (InfinitePlace K)) (hp : p ∈ productUpper (InfinitePlace K)) :
    sourceKPAutomorphicExhaustionCutoff K hζ n
      (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K p)) =
      1 - sourceKPAdelicScalarCutoffProduct K hζ (Real.exp ((n : ℝ) + 1)) (1,qf) p := by
  let x := sourceKPArchEuclideanUpperMap K p
  let a := ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p (fun v => productUpper_pos hp v))
  have hmatrix : sourceKPArchUpperHalfSection K hζ x =
      sourceArchUpperHalfspaceMatrix K hζ p (fun v => productUpper_pos hp v) := by
    have hpoint := sourceKPArchUpperEuclideanMap_right_inverse K p
      (fun v => productUpper_pos hp v)
    rw [← sourceKPArchUpperHalfspaceMatrix_euclidean K hζ x]
    simp only [x, hpoint]
  have hpair : ((1, qf) : SourceKPAdelicProjective K hζ) * (a, 1) = (a, qf) :=
    Prod.ext (one_mul _) (mul_one _)
  rw [sourceKPUpperToCompact_section, sourceKPAutomorphicExhaustionCutoff,
    sourceKPAutomorphicCompactOrbitHeight_mk, sourceKPAutomorphicOrbitHeight_mk,
    sourceKPAdelicScalarCutoffProduct, dite_eq_left (fun v => productUpper_pos hp v),
    sourceKPAdelicScalarCutoff, Real.log_exp, hmatrix, hpair]

theorem sourceKPAutomorphicExhaustionCutoff_chart_eventuallyEq (n : ℕ)
    (qf : SourceKPFiniteAdeleProjective K hζ)
    (p : ProductSpace (InfinitePlace K)) (hp : p ∈ productUpper (InfinitePlace K)) :
    sourceKPCompactChartPullback K hζ
      (fun y => (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ)) (QuotientGroup.mk qf)
      =ᶠ[𝓝 p] fun x => (1 : ℂ) -
        (sourceKPAdelicScalarCutoffProduct K hζ (Real.exp ((n : ℝ) + 1)) (1,qf) x : ℂ) := by
  filter_upwards [sourceKPProductUpper_eventually K p (fun v => productUpper_pos hp v)] with x hx
  have hxu : x ∈ productUpper (InfinitePlace K) := fun v _ => hx v
  change (if x ∈ productUpper (InfinitePlace K) then
    (sourceKPAutomorphicExhaustionCutoff K hζ n
      (sourceKPUpperToCompact K hζ (QuotientGroup.mk qf) (sourceKPArchEuclideanUpperMap K x)) : ℂ)
    else 0) = _
  rw [ite_eq_left hxu,
    sourceKPAutomorphicExhaustionCutoff_upper K hζ n qf x hxu, Complex.ofReal_sub,
    Complex.ofReal_one]

theorem sourceKPAutomorphicExhaustionCutoff_chart_contDiff (n : ℕ)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (sourceKPCompactChartPullback K hζ
      (fun y => (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ)) b)
      (productUpper (InfinitePlace K)) := by
  obtain ⟨qf,rfl⟩ := Quotient.mk_surjective b
  intro p hp
  have hT : 1 < Real.exp ((n : ℝ) + 1) := Real.one_lt_exp_iff.mpr (by positivity)
  have hs := sourceKPAdelicScalarCutoffProduct_contDiffAt K hζ hT (1,qf) p
    (fun v => productUpper_pos hp v)
  have hc : ContDiffAt ℝ (∞ : ℕ∞ω)
      (fun x => (1 : ℂ) -
        (sourceKPAdelicScalarCutoffProduct K hζ (Real.exp ((n : ℝ) + 1)) (1,qf) x : ℂ)) p :=
    contDiffAt_const.sub (Complex.ofRealCLM.contDiff.contDiffAt.comp p hs)
  exact (hc.congr_of_eventuallyEq
    (sourceKPAutomorphicExhaustionCutoff_chart_eventuallyEq K hζ n qf p hp)).contDiffWithinAt

theorem sourceKPAutomorphicExhaustionCutoff_complex_continuous (n : ℕ) :
    Continuous (fun y => (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let m := sourceKPUpperToCompact K hζ b
  let f := fun y => (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ)
  have hpositive (q : SourceKPArchUpperHalfSpace K) :
      sourceKPArchUpperEuclideanMap K q ∈ productUpper (InfinitePlace K) :=
    fun v _ => sourceKPArchUpperEuclidean_positive K q v
  have hcont := (sourceKPAutomorphicExhaustionCutoff_chart_contDiff K hζ n b).continuousOn
    |>.comp_continuous (sourceKPArchUpperEuclideanMap_continuous K) hpositive
  have he : f ∘ m = sourceKPCompactChartPullback K hζ f b ∘
      sourceKPArchUpperEuclideanMap K := by
    funext q
    simp only [Function.comp_apply, sourceKPCompactChartPullback, if_pos (hpositive q)]
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
  have hm : Continuous (f ∘ m) := he.symm ▸ hcont
  have hn : Filter.map m (𝓝 p) = 𝓝 (m p) :=
    (sourceKPUpperToCompact_isOpenMap K hζ b).map_nhds_eq
      (sourceKPUpperToCompact_continuous K hζ b).continuousAt
  change Tendsto f (𝓝 (m p)) (𝓝 (f (m p)))
  rw [← hn, tendsto_map'_iff]
  exact hm.continuousAt

def sourceKPCompactExhaustionCore (n : ℕ) : sourceKPCompactCore K hζ (∞ : ℕ∞ω) :=
  ⟨(fun y => (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ)),
    sourceKPAutomorphicExhaustionCutoff_complex_continuous K hζ n,
    (sourceKPAutomorphicExhaustionCutoff_hasCompactSupport K hζ n).comp_left Complex.ofReal_zero,
    sourceKPAutomorphicExhaustionCutoff_chart_contDiff K hζ n⟩

theorem sourceKPCompactExhaustionCore_apply (n : ℕ)
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    (sourceKPCompactExhaustionCore K hζ n).val y =
      (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ) := rfl

def sourceKPCompactExhaustionC2 (n : ℕ) : sourceKPCompactC2Core K hζ :=
  sourceKPCompactCoreWeaken K hζ (by simp : (2 : ℕ∞ω) ≤ ∞)
    (sourceKPCompactExhaustionCore K hζ n)

theorem sourceKPCompactExhaustionC2_apply (n : ℕ)
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    (sourceKPCompactExhaustionC2 K hζ n).val y =
      (sourceKPAutomorphicExhaustionCutoff K hζ n y : ℂ) := rfl

theorem sourceKPAutomorphicExhaustionCutoff_continuous (n : ℕ) :
    Continuous (sourceKPAutomorphicExhaustionCutoff K hζ n) := by
  simpa only [Function.comp_def, Complex.ofReal_re] using
    Complex.continuous_re.comp (sourceKPAutomorphicExhaustionCutoff_complex_continuous K hζ n)

theorem sourceKPAutomorphicExhaustionCutoff_pos_next_eq_one (n : ℕ)
    (y : SourceKPAutomorphicCompactLevel K hζ)
    (hy : 0 < sourceKPAutomorphicExhaustionCutoff K hζ n y) :
    sourceKPAutomorphicExhaustionCutoff K hζ (n + 1) y = 1 := by
  apply sourceKPAutomorphicExhaustionCutoff_eq_one
  have hlt : Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ y) - ((n : ℝ) + 1) < 1 := by
    by_contra h
    have he := Real.smoothTransition.one_of_one_le (le_of_not_gt h)
    unfold sourceKPAutomorphicExhaustionCutoff at hy
    rw [he] at hy
    linarith
  push_cast
  linarith

theorem sourceKPAutomorphicExhaustionCutoff_eventually_locally_one
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    ∃ N : ℕ, ∀ n ≥ N,
      sourceKPAutomorphicExhaustionCutoff K hζ n =ᶠ[𝓝 y] fun _ => 1 := by
  obtain ⟨N,hN⟩ := exists_nat_ge (Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ y))
  have hNy : sourceKPAutomorphicExhaustionCutoff K hζ N y = 1 :=
    sourceKPAutomorphicExhaustionCutoff_eq_one K hζ N y (by linarith)
  have hnear : ∀ᶠ z in 𝓝 y, 0 < sourceKPAutomorphicExhaustionCutoff K hζ N z :=
    (sourceKPAutomorphicExhaustionCutoff_continuous K hζ N).continuousAt.eventually_const_lt
      (by rw [hNy]; norm_num)
  refine ⟨N + 1, ?_⟩
  intro n hn
  filter_upwards [hnear] with z hz
  have hflat := sourceKPAutomorphicExhaustionCutoff_pos_next_eq_one K hζ N z hz
  exact le_antisymm (sourceKPAutomorphicExhaustionCutoff_le_one K hζ n z)
    (hflat ▸ sourceKPAutomorphicExhaustionCutoff_monotone K hζ z hn)

theorem sourceKPAutomorphicExhaustionCutoff_compact_eventually_locally_one
    (C : Set (SourceKPAutomorphicCompactLevel K hζ)) (hC : IsCompact C) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ C,
      sourceKPAutomorphicExhaustionCutoff K hζ n =ᶠ[𝓝 y] fun _ => 1 := by
  let U (n : ℕ) := {y | 0 < sourceKPAutomorphicExhaustionCutoff K hζ n y}
  have hU (n : ℕ) : IsOpen (U n) :=
    isOpen_lt continuous_const (sourceKPAutomorphicExhaustionCutoff_continuous K hζ n)
  have hcover : C ⊆ ⋃ n, U n := by
    intro y _
    obtain ⟨N,hN⟩ := exists_nat_ge (Real.log (sourceKPAutomorphicCompactOrbitHeight K hζ y))
    refine Set.mem_iUnion.mpr ⟨N,?_⟩
    change 0 < sourceKPAutomorphicExhaustionCutoff K hζ N y
    rw [sourceKPAutomorphicExhaustionCutoff_eq_one K hζ N y (by linarith)]
    norm_num
  obtain ⟨t,ht⟩ := hC.elim_finite_subcover U hU hcover
  refine ⟨t.sup id + 1, ?_⟩
  intro n hn y hy
  obtain ⟨j,hj,hyj⟩ := Set.mem_iUnion₂.mp (ht hy)
  have hjn : j + 1 ≤ n := (Nat.succ_le_succ (Finset.le_sup (f := id) hj)).trans hn
  filter_upwards [(hU j).mem_nhds hyj] with z hz
  have he := sourceKPAutomorphicExhaustionCutoff_pos_next_eq_one K hζ j z hz
  exact le_antisymm (sourceKPAutomorphicExhaustionCutoff_le_one K hζ n z)
    (he ▸ sourceKPAutomorphicExhaustionCutoff_monotone K hζ z hjn)

end
end ArtinMatthews
