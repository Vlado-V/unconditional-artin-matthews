module

public import ArtinMatthews.SourceHyperbolicProductMeasure
public import ArtinMatthews.SourceHyperbolicH1Measure
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

abbrev H1Mass (ι : Type*) [Fintype ι] := Lp ℂ 2 (productVolume ι)
abbrev H1Vector (ι : Type*) := EuclideanSpace ℂ (ι × Fin 3)
abbrev H1Gradient (ι : Type*) [Fintype ι] := Lp (H1Vector ι) 2 (productVolume ι)

def h1Tests (ι : Type*) [Fintype ι] (n : ℕ∞ω) : Submodule ℂ (ProductSpace ι → ℂ) where
  carrier := {f | ContDiff ℝ n f ∧ HasCompactSupport f ∧ tsupport f ⊆ productUpper ι}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro f g ⟨hf,hfc,hfs⟩ ⟨hg,hgc,hgs⟩
    exact ⟨hf.add hg,hfc.add hgc,(tsupport_add f g).trans (Set.union_subset hfs hgs)⟩
  smul_mem' := by
    rintro c f ⟨hf,hfc,hfs⟩
    exact ⟨hf.const_smul c,hfc.smul_left,(tsupport_smul_subset_right (fun _ => c) f).trans hfs⟩

def h1TestMass {n : ℕ∞ω} (f : h1Tests ι n) : H1Mass ι :=
  (h1_compact_memLp f.prop.1.continuous f.prop.2.1 f.prop.2.2 2).toLp f.val

theorem h1TestMass_coe {n : ℕ∞ω} (f : h1Tests ι n) :
    (h1TestMass f : ProductSpace ι → ℂ) =ᵐ[productVolume ι] f.val :=
  (h1_compact_memLp f.prop.1.continuous f.prop.2.1 f.prop.2.2 2).coeFn_toLp

def h1TestMassLinear (ι : Type*) [Fintype ι] (n : ℕ∞ω) : h1Tests ι n →ₗ[ℂ] H1Mass ι where
  toFun := h1TestMass
  map_add' _f _g := MemLp.toLp_add _ _
  map_smul' c _f := MemLp.toLp_const_smul c _

theorem h1TestMass_inner {n : ℕ∞ω} (φ : h1Tests ι n) (f : H1Mass ι) :
    inner ℂ (h1TestMass φ) f = ∫ p, star (φ.val p) * f p ∂productVolume ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h1TestMass_coe φ] with p hp
  rw [hp]
  exact RCLike.inner_apply' _ _

def h1RealTest {n : ℕ∞ω} (g : ProductSpace ι → ℝ) (hg : ContDiff ℝ n g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ productUpper ι) : h1Tests ι n := by
  have he : tsupport (fun p => (g p : ℂ)) = tsupport g := by
    unfold tsupport
    congr 1
    ext p
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  refine ⟨fun p => (g p : ℂ),Complex.ofRealCLM.contDiff.comp hg,?_,?_⟩
  · change IsCompact (tsupport (fun p => (g p : ℂ)))
    rwa [he]
  · rwa [he]

theorem h1_smooth_test_separates (f : H1Mass ι)
    (hf : ∀ (g : ProductSpace ι → ℝ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
      (hs : tsupport g ⊆ productUpper ι),
      inner ℂ (h1TestMass (h1RealTest g hg hc hs)) f = 0) : f=0 := by
  have hz : ∀ᵐ p ∂productVolume ι, p ∈ productUpper ι → f p=0 := by
    apply (productUpper_isOpen ι).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (h1_memLp_locallyIntegrableOn (Lp.memLp f))
    intro g hg hc hs
    have h := hf g hg hc hs
    rw [h1TestMass_inner] at h
    simpa [h1RealTest, RCLike.real_smul_eq_coe_mul] using h
  apply Lp.ext
  filter_upwards [hz,productVolume_ae_upper (ι := ι),Lp.coeFn_zero (E := ℂ) (p := 2) (μ := productVolume ι)] with p hp hu h0
  exact (hp hu).trans h0.symm

theorem h1TestMass_denseRange (n : ℕ∞ω) (hn : n ≤ ∞) :
    DenseRange (h1TestMassLinear ι n) := by
  let R := LinearMap.range (h1TestMassLinear ι n)
  have horth : Rᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    have hz : f=0 := by
      apply h1_smooth_test_separates
      intro g hg hc hs
      have h := (Submodule.mem_orthogonal R f).mp hf
        (h1TestMass (h1RealTest g (hg.of_le hn) hc hs)) ⟨h1RealTest g (hg.of_le hn) hc hs,rfl⟩
      exact h
    change f = 0
    exact hz
  have htop : R.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htop

end
end ArtinMatthews.SourceHyperbolicGreen
