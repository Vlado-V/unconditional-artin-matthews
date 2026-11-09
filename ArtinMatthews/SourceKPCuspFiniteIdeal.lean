module

public import ArtinMatthews.SourceKPFiniteCuspPeriod
public import ArtinMatthews.SourceAdelicFundamentalDomain


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite principal ideal used for a cusp torus sublevel. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K)

def sourceKPCuspFiniteScale : 𝔸ᶠ[K] →+ 𝔸ᶠ[K] where
  toFun x := algebraMap K 𝔸ᶠ[K] (d : K) * x
  map_zero' := mul_zero _
  map_add' _ _ := mul_add _ _ _

def sourceKPCuspFiniteIdeal : AddSubgroup 𝔸ᶠ[K] :=
  (sourceKPIntegralFiniteRing K).toAddSubgroup.map (sourceKPCuspFiniteScale K d)

lemma sourceKPCuspFiniteIdeal_mem (x : 𝔸ᶠ[K]) :
    x ∈ sourceKPCuspFiniteIdeal K d ↔
      ∃ y : sourceKPIntegralFiniteRing K, algebraMap K 𝔸ᶠ[K] (d : K) * (y : 𝔸ᶠ[K]) = x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy⟩, hxy⟩
  · rintro ⟨y, hxy⟩
    exact ⟨y, y.property, hxy⟩

omit [NumberField K] in
lemma sourceKPCuspInteger_ne_zero (hd : d ≠ 0) : (d : K) ≠ 0 := by exact_mod_cast hd

def sourceKPCuspFiniteScaleHomeomorph (hd : d ≠ 0) : 𝔸ᶠ[K] ≃ₜ 𝔸ᶠ[K] where
  toFun := sourceKPCuspFiniteScale K d
  invFun x := algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * x
  left_inv x := by
    change algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * (algebraMap K 𝔸ᶠ[K] (d : K) * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), map_one, one_mul]
  right_inv x := by
    change algebraMap K 𝔸ᶠ[K] (d : K) * (algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), map_one, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

lemma sourceKPCuspFiniteIdeal_isOpen (hd : d ≠ 0) : IsOpen (sourceKPCuspFiniteIdeal K d : Set 𝔸ᶠ[K]) := by
  rw [sourceKPCuspFiniteIdeal, AddSubgroup.coe_map]
  exact (sourceKPCuspFiniteScaleHomeomorph K d hd).isOpenMap _ (sourceKPIntegralFiniteRing_isOpen K)

lemma sourceKPCuspFiniteIdeal_isCompact (hd : d ≠ 0) : IsCompact (sourceKPCuspFiniteIdeal K d : Set 𝔸ᶠ[K]) := by
  rw [sourceKPCuspFiniteIdeal, AddSubgroup.coe_map]
  exact (sourceKPIntegralFiniteRing_isCompact K).image (sourceKPCuspFiniteScaleHomeomorph K d hd).continuous

lemma sourceKPCuspFiniteIdeal_rational (hd : d ≠ 0) (q : K) :
    algebraMap K 𝔸ᶠ[K] q ∈ sourceKPCuspFiniteIdeal K d ↔
      ∃ r : 𝓞 K, (d : K) * (r : K) = q := by
  rw [sourceKPCuspFiniteIdeal_mem]
  constructor
  · rintro ⟨x, hx⟩
    have he : algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹ * q) = (x : 𝔸ᶠ[K]) := by
      rw [map_mul, ← hx, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), map_one, one_mul]
    have hmem : algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹ * q) ∈ IntegralAdeles.Construction.finiteIntegralRing K := by
      rw [he]
      exact (sourceKPIntegralFiniteRing_mem K x.val).mp x.property
    obtain ⟨r, hr⟩ := (IntegralAdeles.Construction.rational_mem_finiteIntegral_iff K _).mp hmem
    refine ⟨r, ?_⟩
    change (r : K) = (d : K)⁻¹ * q at hr
    rw [hr, ← mul_assoc, mul_inv_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), one_mul]
  · rintro ⟨r, rfl⟩
    have hr : algebraMap K 𝔸ᶠ[K] (r : K) ∈ sourceKPIntegralFiniteRing K := by
      apply (sourceKPIntegralFiniteRing_mem K _).mpr
      intro P
      exact HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := K) P r
    exact ⟨⟨_, hr⟩, (map_mul (algebraMap K 𝔸ᶠ[K]) _ _).symm⟩

lemma sourceKPCuspFiniteIdeal_remainder (hd : d ≠ 0) (a : 𝔸ᶠ[K]) :
    ∃ q : K, a - algebraMap K 𝔸ᶠ[K] q ∈ sourceKPCuspFiniteIdeal K d := by
  obtain ⟨q, hq⟩ := CompactQuotient.Construction.exists_rational_finite_integral_remainder K
    (algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * a)
  have hmem : algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * a - algebraMap K 𝔸ᶠ[K] q ∈ sourceKPIntegralFiniteRing K :=
    (sourceKPIntegralFiniteRing_mem K _).mpr hq
  refine ⟨(d : K) * q, (sourceKPCuspFiniteIdeal_mem K d _).mpr ⟨⟨_, hmem⟩, ?_⟩⟩
  rw [mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (sourceKPCuspInteger_ne_zero K d hd),
    map_one, one_mul, map_mul]

end
end ArtinMatthews
