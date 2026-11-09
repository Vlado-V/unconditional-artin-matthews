module

public import ArtinMatthews.VaryingKummerAnalyticMixedMellinResidues
public import ArtinMatthews.VaryingKummerAnalyticMeromorphicRegularization


set_option backward.privateInPublic true
@[expose] public section

/-! Actual local principal parts of the smoothed Dedekind logarithmic derivative. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set Filter
open scoped Classical Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedDedekindZeta_order_ne_top (z : ℂ) :
    meromorphicOrderAt (mixedDedekindZeta K) z ≠ ⊤ := by
  apply (mixedDedekindZeta_meromorphic K).exists_meromorphicOrderAt_ne_top_iff_forall.mp
  refine ⟨2,?_⟩
  have hn : mixedDedekindZeta K 2 ≠ 0 := by
    rw [mixedDedekindZeta_eq K (by norm_num : 1 < (2 : ℂ).re)]
    exact dedekindZeta_ne_zero_of_one_lt_re K (by norm_num)
  rw [(mixedDedekindZeta_analyticAt K (by norm_num : (2 : ℂ) ≠ 1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn]
  simp

/-- Signed order of the actual continued Dedekind zeta: negative at its pole. -/
def mixedDedekindOrder (z : ℂ) : ℤ := (meromorphicOrderAt (mixedDedekindZeta K) z).untop₀

theorem mixedDedekindOrder_coe (z : ℂ) :
    (mixedDedekindOrder K z : WithTop ℤ) = meromorphicOrderAt (mixedDedekindZeta K) z :=
  WithTop.coe_untop₀_of_ne_top (mixedDedekindZeta_order_ne_top K z)

theorem mixedDedekindOrder_one : mixedDedekindOrder K 1 = -1 := by
  unfold mixedDedekindOrder
  rw [mixedDedekindZeta_order_one]
  rfl

theorem mixedDedekindOrder_zero : mixedDedekindOrder K 0 =
    (InfinitePlace.nrRealPlaces K : ℤ)+InfinitePlace.nrComplexPlaces K-1 := by
  unfold mixedDedekindOrder
  rw [mixedDedekindZeta_meromorphicOrder_zero]
  rfl

theorem mixedDedekindOrder_xi_zero {ρ : ℂ} (hρ : mixedCompletedDedekindXi K ρ = 0) :
    mixedDedekindOrder K ρ =
      OAI.PrimeDegreePackets.AnalyticGrowth.zeroMultiplicity (mixedCompletedDedekindXi K) ρ := by
  unfold mixedDedekindOrder
  rw [mixedDedekindZeta_order_at_xi_zero K hρ]
  rfl

variable (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
  (hpositive : tsupport f ⊆ Ioi 0) (hcontinuous : Continuous f)
  {x : ℝ} (hx : 0 < x)
include hcompact hpositive hcontinuous hx

theorem mixedExplicitFormulaIntegrand_regular_part (z : ℂ) :
    ∃ R : ℂ → ℂ,AnalyticAt ℂ R z ∧
      (fun s => mixedExplicitFormulaIntegrand K f x s+
        (mixedDedekindOrder K z : ℂ)*(mellin f z*(x : ℂ)^z)/(s-z)) =ᶠ[𝓝[≠] z] R := by
  let W : ℂ → ℂ := fun s => mellin f s*(x : ℂ)^s
  have hW : AnalyticAt ℂ W z :=
    ((smoothMellin_entire f hcompact hpositive hcontinuous).mul
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))).analyticAt z
  obtain ⟨R,hR,he⟩ := meromorphic_weighted_logDeriv_regular_part
    (mixedDedekindZeta_meromorphic K z) (mixedDedekindOrder_coe K z).symm hW
  refine ⟨R,hR,?_⟩
  filter_upwards [he] with s hs
  dsimp only [W] at hs
  rw [← hs]
  unfold mixedExplicitFormulaIntegrand
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
