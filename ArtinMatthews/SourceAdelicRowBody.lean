module

public import ArtinMatthews.SourceAdelicBlichfeldt


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed adelic row body of mass two, with integral finite coordinates
and uniformly bounded archimedean differences. -/
namespace ArtinMatthews
open NumberField MeasureTheory Set
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local instance sourceAdelicRowBody_measurableSpace : MeasurableSpace 𝔸[F] := borel 𝔸[F]
local instance sourceAdelicRowBody_borelSpace : BorelSpace 𝔸[F] := ⟨rfl⟩
local instance sourceAdelicRowBody_sFinite : SFinite (sourceKPAdelicStandardHaar F) := by
  unfold sourceKPAdelicStandardHaar
  infer_instance
local notation "D" => sourceKPAdelicFundamentalDomain F
local notation "I" => IntegralAdeles.Construction.finiteIntegralRing F

def sourceKPAdelicEnlargedDomain : Set 𝔸[F] := D ∪ {x | x - 1 ∈ D}

def sourceKPAdelicBlichfeldtBody : Set (𝔸[F] × 𝔸[F]) := sourceKPAdelicEnlargedDomain F ×ˢ D

theorem sourceKPAdelicEnlargedDomain_measurable : MeasurableSet (sourceKPAdelicEnlargedDomain F) :=
  (sourceKPAdelicFundamentalDomain_measurable F).union
    ((sourceKPAdelicFundamentalDomain_measurable F).preimage
      (continuous_id.sub continuous_const).measurable)

theorem sourceKPAdelicBlichfeldtBody_measurable : MeasurableSet (sourceKPAdelicBlichfeldtBody F) :=
  (sourceKPAdelicEnlargedDomain_measurable F).prod (sourceKPAdelicFundamentalDomain_measurable F)

theorem sourceKPAdelicEnlargedDomain_mass :
    sourceKPAdelicStandardHaar F (sourceKPAdelicEnlargedDomain F) = 2 := by
  have hd : Disjoint D {x : 𝔸[F] | x - 1 ∈ D} := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change x - 1 ∈ D at hy
    obtain ⟨q, hq, hu⟩ := sourceKPAdelicFundamentalDomain_unique F x
    have hx0 : x - algebraMap F 𝔸[F] (0 : F) ∈ D := by
      simpa only [map_zero, sub_zero] using hx
    have hx1 : x - algebraMap F 𝔸[F] (1 : F) ∈ D := by
      simpa only [map_one] using hy
    have h0 : (0 : F) = q := hu 0 hx0
    have h1 : (1 : F) = q := hu 1 hx1
    exact zero_ne_one (h0.trans h1.symm)
  have ht : sourceKPAdelicStandardHaar F {x : 𝔸[F] | x - 1 ∈ D} = 1 := by
    simp only [sub_eq_add_neg]
    change sourceKPAdelicStandardHaar F ((fun x : 𝔸[F] => x + (-1)) ⁻¹' D) = 1
    rw [measure_preimage_add_right, sourceKPAdelicStandardHaar_fundamentalDomain]
  rw [sourceKPAdelicEnlargedDomain, measure_union hd
    ((sourceKPAdelicFundamentalDomain_measurable F).preimage
      (continuous_id.sub continuous_const).measurable),
    sourceKPAdelicStandardHaar_fundamentalDomain, ht]
  norm_num

theorem sourceKPAdelicBlichfeldtBody_mass :
    sourceKPAdelicRowHaar F (sourceKPAdelicBlichfeldtBody F) = 2 := by
  rw [sourceKPAdelicRowHaar, sourceKPAdelicBlichfeldtBody, Measure.prod_prod,
    sourceKPAdelicEnlargedDomain_mass, sourceKPAdelicStandardHaar_fundamentalDomain, mul_one]

theorem sourceKPAdelicEnlargedDomain_integral {x : 𝔸[F]}
    (hx : x ∈ sourceKPAdelicEnlargedDomain F) : x.2 ∈ I := by
  rcases hx with hx | hx
  · exact hx.2
  · have h : (x - 1).2 ∈ I := hx.2
    change x.2 - 1 ∈ I at h
    have hi := (IntegralAdeles.Construction.finiteIntegralRing F).add_mem h
      (IntegralAdeles.Construction.finiteIntegralRing F).one_mem
    simpa only [sub_add_cancel] using hi

theorem sourceKPAdelicBlichfeldtBody_diff_integral {x y : 𝔸[F] × 𝔸[F]}
    (hx : x ∈ sourceKPAdelicBlichfeldtBody F) (hy : y ∈ sourceKPAdelicBlichfeldtBody F) :
    (y.1 - x.1).2 ∈ I ∧ (y.2 - x.2).2 ∈ I := by
  exact ⟨(IntegralAdeles.Construction.finiteIntegralRing F).sub_mem (sourceKPAdelicEnlargedDomain_integral F hy.1)
    (sourceKPAdelicEnlargedDomain_integral F hx.1), (IntegralAdeles.Construction.finiteIntegralRing F).sub_mem hy.2.2 hx.2.2⟩

theorem sourceKPAdelicBlichfeldtBody_diff_arch_bound :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ sourceKPAdelicBlichfeldtBody F,
      ∀ y ∈ sourceKPAdelicBlichfeldtBody F, ∀ v : InfinitePlace F,
        ‖(y.1 - x.1).1 v‖ ≤ R ∧ ‖(y.2 - x.2).1 v‖ ≤ R := by
  have hlocal (v : InfinitePlace F) : ∃ C : ℝ,
      ∀ x ∈ CompactQuotient.Construction.adelicCompactRepresentatives F, ‖x.1 v‖ ≤ C :=
    (CompactQuotient.Construction.isCompact_adelicCompactRepresentatives F).exists_bound_of_continuousOn
        (f := fun x : 𝔸[F] => x.1 v) ((continuous_apply v).comp continuous_fst).continuousOn
  choose C hC using hlocal
  let B := max 1 (∑ v : InfinitePlace F, |C v|)
  have hB : 1 ≤ B := le_max_left _ _
  have hCB (v : InfinitePlace F) : C v ≤ B := by
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun w _ => abs_nonneg (C w))
      (Finset.mem_univ v)).trans (le_max_right _ _))
  have hD {x : 𝔸[F]} (hx : x ∈ D) (v : InfinitePlace F) : ‖x.1 v‖ ≤ B :=
    (hC v x (sourceKPAdelicFundamentalDomain_subset_compact F hx)).trans (hCB v)
  have hE {x : 𝔸[F]} (hx : x ∈ sourceKPAdelicEnlargedDomain F) (v : InfinitePlace F) :
      ‖x.1 v‖ ≤ B + 1 := by
    rcases hx with hx | hx
    · exact (hD hx v).trans (by linarith)
    · calc
        ‖x.1 v‖ = ‖(x - 1).1 v + 1‖ := by congr 1; change x.1 v = (x.1 v - 1) + 1; abel
        _ ≤ ‖(x - 1).1 v‖ + ‖(1 : v.Completion)‖ := norm_add_le _ _
        _ ≤ B + 1 := by simpa only [norm_one, add_comm] using add_le_add_right (hD hx v) 1
  refine ⟨2 * (B + 1), by linarith, ?_⟩
  intro x hx y hy v
  have hx1 := hE hx.1 v
  have hy1 := hE hy.1 v
  have hx2 := hE (Or.inl hx.2) v
  have hy2 := hE (Or.inl hy.2) v
  constructor
  · exact (norm_sub_le (y.1.1 v) (x.1.1 v)).trans (by linarith)
  · exact (norm_sub_le (y.2.1 v) (x.2.1 v)).trans (by linarith)

end
end ArtinMatthews
