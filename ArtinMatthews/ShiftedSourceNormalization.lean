module

public import ArtinMatthews.ShiftedSourceCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Normalized compact Schwartz sources for the shifted correlation.
The additive shift by one becomes a bounded translation δ=1/(mT), whose
Schwartz seminorms are controlled uniformly when mT≥1. -/

noncomputable section
open Complex Real Set
open scoped ContDiff

namespace ArtinMatthews

/-- Translation uses Mathlib's actual Schwartz composition operator. -/
def shiftedSourceTranslate (W : SchwartzMap ℝ ℂ) (δ : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ ↦ x + (-δ))
    (by fun_prop) (isometry_add_right (-δ)).antilipschitzWith W

@[simp] theorem shiftedSourceTranslate_apply (W : SchwartzMap ℝ ℂ) (δ x : ℝ) :
    shiftedSourceTranslate W δ x = W (x-δ) := rfl

theorem shiftedSourceTranslate_support (W : SchwartzMap ℝ ℂ) (a b δ : ℝ)
    (hW : Function.support W ⊆ Icc a b) :
    Function.support (shiftedSourceTranslate W δ) ⊆ Icc (a+δ) (b+δ) := by
  intro x hx
  have h := hW hx
  change a ≤ x-δ ∧ x-δ ≤ b at h
  constructor <;> linarith [h.1,h.2]

private theorem iteratedDeriv_zero_off_tsupport (W : SchwartzMap ℝ ℂ) (j : ℕ) (x : ℝ)
    (hx : x ∉ tsupport W) : iteratedDeriv j W x = 0 := by
  have hz : iteratedFDeriv ℝ j W x = 0 := by
    by_contra h
    exact hx (support_iteratedFDeriv_subset j h)
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hz, norm_zero]

/-- Bounded translations of a positive compact source have uniform Schwartz
seminorms. Only the original order-j derivative supremum is needed. -/
theorem shiftedSourceTranslate_seminorm (W : SchwartzMap ℝ ℂ) (B δ : ℝ)
    (hB : 0 ≤ B) (hW : Function.support W ⊆ Icc 0 B) (hδ : δ ∈ Icc 0 1) (k j : ℕ) :
    SchwartzMap.seminorm ℝ k j (shiftedSourceTranslate W δ) ≤
      (B+1)^k * SchwartzMap.seminorm ℝ 0 j W := by
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro x
  have he : iteratedDeriv j (shiftedSourceTranslate W δ) x = iteratedDeriv j W (x-δ) := by
    change iteratedDeriv j (fun z ↦ W (z-δ)) x = _
    rw [iteratedDeriv_comp_sub_const]
  rw [he]
  by_cases hx : x-δ ∈ tsupport W
  · have hc : tsupport W ⊆ Icc 0 B := closure_minimal hW isClosed_Icc
    have hb := hc hx
    have ha : |x| ≤ B+1 := by rw [abs_le]; constructor <;> linarith [hb.1,hb.2,hδ.1,hδ.2]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (abs_nonneg x) ha k
    · simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 j W (x-δ)
    · exact norm_nonneg _
    · positivity
  · rw [iteratedDeriv_zero_off_tsupport W j (x-δ) hx, norm_zero, mul_zero]
    positivity

/-- Rescaling the original source places its support in [1,2]. -/
theorem normalizedSource_support (g : ℝ → ℂ) (T : ℝ) (hT : 0 < T)
    (hg : Function.support g ⊆ Icc T (2*T)) :
    Function.support (fun x : ℝ ↦ g (T*x)) ⊆ Icc 1 2 := by
  intro x hx
  have h := hg hx
  change T ≤ T*x ∧ T*x ≤ 2*T at h
  constructor <;> nlinarith [h.1,h.2]

/-- The normalized source is an actual Schwartz function, constructed from
its proved compact support and the smoothness of g. -/
def normalizedSourceSchwartz (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (T : ℝ) (hT : 0 < T)
    (hgs : Function.support g ⊆ Icc T (2*T)) : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (normalizedSource_support g T hT hgs)).toSchwartzMap (hg.comp (by fun_prop))

@[simp] theorem normalizedSourceSchwartz_apply (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (T : ℝ) (hT : 0 < T) (hgs : Function.support g ⊆ Icc T (2*T)) (x : ℝ) :
    normalizedSourceSchwartz g hg T hT hgs x = g (T*x) := rfl

/-- The fixed plateau also gives an actual compact Schwartz source. -/
def sourcePlateauSchwartz : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc shiftedSourcePlateau_support).toSchwartzMap
    shiftedSourcePlateau_smooth

@[simp] theorem sourcePlateauSchwartz_apply (x : ℝ) : sourcePlateauSchwartz x = shiftedSourcePlateau x := rfl

/-- Exact normalized representation of H1 at the natural length mT. -/
theorem shiftedSourceTest_eq_normalized (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (T m : ℝ) (hT : 0 < T) (hm : 0 < m) (hgs : Function.support g ⊆ Icc T (2*T)) (x : ℝ) :
    shiftedSourceTest g m x =
      shiftedSourceTranslate (normalizedSourceSchwartz g hg T hT hgs) (1/(m*T)) (x/(m*T)) := by
  simp only [shiftedSourceTranslate_apply, normalizedSourceSchwartz_apply, shiftedSourceTest]
  congr 1
  field_simp

/-- Exact normalized representation of H2, with the same bounded translation. -/
theorem shiftedSourceMajorant_eq_normalized (m T x : ℝ) :
    shiftedSourceMajorant m T x =
      shiftedSourceTranslate sourcePlateauSchwartz (1/(m*T)) (x/(m*T)) := by
  simp only [shiftedSourceTranslate_apply, sourcePlateauSchwartz_apply, shiftedSourceMajorant]
  congr 1
  ring

/-- The first normalized shifted source has uniformly bounded support. -/
theorem shiftedSourceTest_normalized_support (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (T m : ℝ) (hT : 0 < T) (hgs : Function.support g ⊆ Icc T (2*T)) (hscale : 1 ≤ m*T) :
    Function.support (shiftedSourceTranslate (normalizedSourceSchwartz g hg T hT hgs) (1/(m*T))) ⊆
      Icc 0 3 := by
  have hmT : 0 < m*T := by linarith
  have hδ : 1/(m*T) ∈ Icc 0 1 := ⟨by positivity, (div_le_one hmT).mpr hscale⟩
  intro x hx
  have h := shiftedSourceTranslate_support (normalizedSourceSchwartz g hg T hT hgs)
    1 2 (1/(m*T)) (normalizedSource_support g T hT hgs) hx
  constructor <;> linarith [h.1,h.2,hδ.1,hδ.2]

/-- The second normalized shifted source has uniformly bounded support. -/
theorem shiftedSourceMajorant_normalized_support (m T : ℝ) (hscale : 1 ≤ m*T) :
    Function.support (shiftedSourceTranslate sourcePlateauSchwartz (1/(m*T))) ⊆ Icc 0 (7/2) := by
  have hmT : 0 < m*T := by linarith
  have hδ : 1/(m*T) ∈ Icc 0 1 := ⟨by positivity, (div_le_one hmT).mpr hscale⟩
  intro x hx
  have h := shiftedSourceTranslate_support sourcePlateauSchwartz (1/2) (5/2) (1/(m*T))
    shiftedSourcePlateau_support hx
  constructor <;> linarith [h.1,h.2,hδ.1,hδ.2]

/-- Uniform source seminorms for H1 follow from the prescribed derivatives
of g, without constants depending on m or T. -/
theorem shiftedSourceTest_normalized_seminorm (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (T m C : ℝ) (hT : 0 < T) (hgs : Function.support g ⊆ Icc T (2*T))
    (hscale : 1 ≤ m*T) (k j : ℕ) (hC : 0 ≤ C)
    (hderiv : ∀ x : ℝ, ‖iteratedDeriv j g x‖ ≤ C/T^j) :
    SchwartzMap.seminorm ℝ k j
      (shiftedSourceTranslate (normalizedSourceSchwartz g hg T hT hgs) (1/(m*T))) ≤ 3^k*C := by
  let W := normalizedSourceSchwartz g hg T hT hgs
  have hW : Function.support W ⊆ Icc 0 2 :=
    (normalizedSource_support g T hT hgs).trans (by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩)
  have hbase : SchwartzMap.seminorm ℝ 0 j W ≤ C := by
    apply SchwartzMap.seminorm_le_bound' ℝ 0 j W hC
    intro x
    have he : iteratedDeriv j W x = T^j • iteratedDeriv j g (T*x) := by
      have hh := congrArg (fun h : ℝ → ℂ ↦ h x)
        (iteratedDeriv_comp_const_smul (n := j) (hg.of_le (by simp)) T)
      change iteratedDeriv j (fun y : ℝ ↦ g (T*y)) x = _
      simpa only [smul_eq_mul] using hh
    rw [pow_zero,one_mul,he,norm_smul,Real.norm_eq_abs,abs_pow,abs_of_pos hT]
    have hh := mul_le_mul_of_nonneg_left (hderiv (T*x)) (pow_nonneg hT.le j)
    convert hh using 1
    field_simp
  have hmT : 0 < m*T := by linarith
  have hs := shiftedSourceTranslate_seminorm W 2 (1/(m*T)) (by norm_num) hW
    ⟨by positivity,(div_le_one hmT).mpr hscale⟩ k j
  norm_num only [show (2 : ℝ)+1=3 by norm_num] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hbase (by positivity))

end ArtinMatthews
