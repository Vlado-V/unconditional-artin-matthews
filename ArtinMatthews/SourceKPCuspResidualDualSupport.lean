module

public import ArtinMatthews.SourceKPCuspNativeTraceSlice
public import ArtinMatthews.SourceKPCuspTraceModeDictionary
public import ArtinMatthews.SourceKPCuspResidualFourierUpper
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical residual coefficient is supported on the trace dual
of the original fixed principal period. The finite phase is forced by
the actual level lift at that same period. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField AdeleRing MatrixGroups nonZeroDivisors
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

theorem sourceKPCuspResidualFourierValue_finite_period_of_ne_zero
    (d : 𝓞 K) (qf : Gf) (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (hm : sourceKPCuspResidualFourierValue K hζ m hT qf ≠ 0)
    {t : 𝔸ᶠ[K]} (ht : t ∈ sourceKPCuspFiniteIdeal K d) :
    finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m : K) * t) = 1 := by
  obtain ⟨k, hk⟩ := hperiod t ht
  have hfinite : qf⁻¹ * Nf t * qf = sourceKPFiniteLevelLift K hζ k :=
    congrArg (fun g : SourceKPAdelicProjective K hζ => g.2) hk
  have hmove : Nf t * qf = qf * sourceKPFiniteLevelLift K hζ k := by
    calc
      _ = qf * (qf⁻¹ * Nf t * qf) := by group
      _ = _ := congrArg (fun a : Gf => qf * a) hfinite
  have hphase := sourceKPCuspResidualFourierValue_left_finite_upper K hζ m hT qf t
  rw [hmove, sourceKPCuspResidualFourierValue_right_deep] at hphase
  exact mul_right_cancel₀ hm (hphase.symm.trans (one_mul _).symm)

theorem sourceKPCuspResidualFourierValue_mem_dual_of_ne_zero
    (d : 𝓞 K) (hd : d ≠ 0) (qf : Gf)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (hm : sourceKPCuspResidualFourierValue K hζ m hT qf ≠ 0) :
    (m : K) ∈ D[d] := by
  apply (sourceKPCuspTraceDualFrequency_period_iff K d hd (m : K)).1
  intro z hz
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.mp hz
  have hft : character K (algebraMap K 𝔸[K] (m : K) * sourceKPFiniteAddEmbedding K t) = 1 := by
    rw [show algebraMap K 𝔸[K] (m : K) * sourceKPFiniteAddEmbedding K t =
      ((0, algebraMap K 𝔸ᶠ[K] (m : K) * t) : 𝔸[K]) from Prod.ext (mul_zero _) rfl,
      character_finite]
    exact sourceKPCuspResidualFourierValue_finite_period_of_ne_zero K hζ d qf hperiod m hT hm ht
  change character K (algebraMap K 𝔸[K] (m : K) *
    (algebraMap K 𝔸[K] a + sourceKPFiniteAddEmbedding K t)) = 1
  rw [mul_add, AddChar.map_add_eq_mul, ← map_mul (algebraMap K 𝔸[K]) (m : K) a,
    character_principal, hft, one_mul]

theorem sourceKPCuspResidualFourierValue_eq_zero_of_not_mem_dual
    (d : 𝓞 K) (hd : d ≠ 0) (qf : Gf)
    (hperiod : sourceKPCuspNativeFinitePeriod K hζ d qf)
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (hm : (m : K) ∉ D[d]) :
    sourceKPCuspResidualFourierValue K hζ m hT qf = 0 := by
  by_contra hne
  exact hm (sourceKPCuspResidualFourierValue_mem_dual_of_ne_zero K hζ d hd qf hperiod m hT hne)

end
end ArtinMatthews
