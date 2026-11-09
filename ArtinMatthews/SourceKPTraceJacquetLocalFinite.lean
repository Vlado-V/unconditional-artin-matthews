module

public import ArtinMatthews.SourceKPTraceJacquetLocalCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The true local ordinary integral in Re(s)>0 equals a finite
entire expression. The same expression is the stabilized compact
truncation at every parameter, including the exceptional target. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical Filter
open VaryingKummerAnalytic
open scoped NumberField Classical Topology BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "B₀" => sourceLocalBall K P.val
local notation "shell₀" => sourceJacquetValuationShell K P.val
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

def sourceKPTraceJacquetLocalShellTerm (s : ℂ) (m : L) (l : ℕ) : ZMod 3 → ℂ :=
  (Complex.exp (-2*s*(l : ℂ)*(Real.log Q₀ : ℂ)) *
    sourceJacquetShellIntegral K P.val (sourceJacquetShellCharacter K P.val χ₀ l)
      (m * ((π₀^(-(l : ℤ)) : Lˣ) : L))) • sourceJacquetBasis ((2*(l : ℤ) : ℤ) : ZMod 3)

def sourceKPTraceJacquetLocalFiniteValue (s : ℂ) (m : Lˣ) : ZMod 3 → ℂ :=
  (if ν₀ (m : L) ≤ 1 then (1 : ℂ) else 0) • sourceJacquetBasis 0 +
    ∑ l ∈ Finset.Icc 1 (sourceKPTraceJacquetLocalRadius K P.val m),
      sourceKPTraceJacquetLocalShellTerm K hζ S₀ P s (m : L) l

theorem sourceKPTraceJacquetLocalOrdinary_truncated (hP : P.val ∉ traceBadPlaces K)
    (s : ℂ) (m : L) (N : ℕ) :
    IntegrableOn (sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m) (B₀ (N : ℤ)) μ₀ ∧
    (∫ x in B₀ (N : ℤ), sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m x ∂μ₀) =
      (if ν₀ m ≤ 1 then (1 : ℂ) else 0) • sourceJacquetBasis 0 +
        ∑ l ∈ Finset.Icc 1 N, sourceKPTraceJacquetLocalShellTerm K hζ S₀ P s m l := by
  let c : L → ℂ := fun x => ψ₀ (-(m*x))
  let f : L → ZMod 3 → ℂ := sourceKPTameIntertwiningIntegrand K hζ S₀ P s
  let F := sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s m
  let : (μ₀).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar K P.val
  have hc : Continuous c :=
    (localFiniteCharacter_continuous K P.val).comp (continuous_const.mul continuous_id).neg
  have hw (μ : Measure L) (hf : Integrable f μ) : Integrable F μ := by
    change Integrable (fun x => c x • f x) μ
    refine hf.mono (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul, show ‖c x‖ = 1 from localFiniteCharacter_unitary K P.val (-(m*x)), one_mul]
  have hf0 : IntegrableOn f (B₀ 0) μ₀ :=
    ((continuous_const : Continuous (fun _ : L => sourceJacquetBasis (0 : ZMod 3))).continuousOn.integrableOn_compact
      (μ := μ₀) (sourceLocalBall_isCompact K P.val 0)).congr_fun
      (fun x hx => (sourceKPTameIntertwiningIntegrand_on_zero K hζ S₀ P s x hx).symm)
      (sourceLocalBall_isCompact K P.val 0).measurableSet
  have h := sourceJacquetBall_integral_shells K P.val F
    (hw _ hf0) (fun l _ => hw _ (sourceKPTameIntertwiningIntegral_shell K hζ S₀ P hP s l).1) N
  refine ⟨h.1,?_⟩
  change (∫ x in B₀ (N : ℤ), F x ∂μ₀) = _
  rw [h.2, sourceKPTraceJacquetLocalOrdinary_integer_ball K hζ S₀ P hP s m]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact sourceKPTraceJacquetLocalOrdinary_shell K hζ S₀ P hP s m l

theorem sourceKPTraceJacquetLocalOrdinary_truncated_stable (hP : P.val ∉ traceBadPlaces K)
    (s : ℂ) (m : Lˣ) (N : ℕ) (hN : sourceKPTraceJacquetLocalRadius K P.val m ≤ N) :
    (∫ x in B₀ (N : ℤ), sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s (m : L) x ∂μ₀) =
      sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s m := by
  let R := sourceKPTraceJacquetLocalRadius K P.val m
  let f := sourceKPTraceJacquetLocalShellTerm K hζ S₀ P s (m : L)
  rw [(sourceKPTraceJacquetLocalOrdinary_truncated K hζ S₀ P hP s (m : L) N).2,
    sourceKPTraceJacquetLocalFiniteValue]
  congr 1
  symm
  apply Finset.sum_subset (show Finset.Icc 1 R ⊆ Finset.Icc 1 N from
    fun l hl => Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hl).1, (Finset.mem_Icc.mp hl).2.trans hN⟩)
  intro l hl hnot
  have hR : R < l := lt_of_not_ge fun hle => hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hl).1,hle⟩)
  change f l = 0
  exact (sourceKPTraceJacquetLocalOrdinary_shell K hζ S₀ P hP s (m : L) l).symm.trans
    (sourceKPTraceJacquetLocalOrdinary_shell_zero K hζ S₀ P hP s m l hR)

theorem sourceKPTraceJacquetLocalOrdinary_eq_finite (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) (m : Lˣ) :
    sourceKPTraceJacquetLocalOrdinary K hζ S₀ P s (m : L) =
      sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s m := by
  let F := sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s (m : L)
  let B := fun N : ℕ => B₀ (N : ℤ)
  have hcover : (⋃ N : ℕ, B N) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨N,hN⟩ := (sourceJacquetBall_eventually_contains K P.val x).exists
    exact Set.mem_iUnion.mpr ⟨N,hN⟩
  have hmono : Monotone B := by
    intro a b hab x hx
    exact (show ν₀ x ≤ WithZero.exp (a : ℤ) from hx).trans
      (WithZero.exp_le_exp.mpr (by exact_mod_cast hab))
  have hF : IntegrableOn F (⋃ N : ℕ, B N) μ₀ := by
    rw [hcover, integrableOn_univ]
    exact sourceKPTraceJacquetLocalOrdinaryIntegrand_integrable K hζ S₀ P hP hs (m : L)
  have hB (N : ℕ) : MeasurableSet (B N) :=
    (sourceLocalBall_isCompact K P.val (N : ℤ)).measurableSet
  have hlim := tendsto_setIntegral_of_monotone hB hmono hF
  rw [hcover, setIntegral_univ] at hlim
  have hstable : Tendsto (fun N : ℕ => ∫ x in B N, F x ∂μ₀) atTop
      (𝓝 (sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s m)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (sourceKPTraceJacquetLocalRadius K P.val m)] with N hN
    exact (sourceKPTraceJacquetLocalOrdinary_truncated_stable K hζ S₀ P hP s m N hN).symm
  exact tendsto_nhds_unique hlim hstable

theorem sourceKPTraceJacquetLocalFiniteValue_entire (m : Lˣ) :
    Differentiable ℂ (fun s => sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s m) := by
  unfold sourceKPTraceJacquetLocalFiniteValue
  apply Differentiable.add (differentiable_const _)
  apply Differentiable.fun_sum
  intro l _
  unfold sourceKPTraceJacquetLocalShellTerm
  fun_prop

end
end ArtinMatthews
