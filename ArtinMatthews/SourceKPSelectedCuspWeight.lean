module

public import ArtinMatthews.SourceKPSelectedCuspBand
public import ArtinMatthews.SourceKPCuspLevelCover
public import ArtinMatthews.SourceKPAdelicCuspBand


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded positive-mass test on a single cusp, with exact upper invariance. -/

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Xf" => SourceKPFiniteLevelSpace K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "HF" => sourceKPFiniteLevelHeight K hζ
local notation "HC" => sourceKPAdelicCoverHeight K hζ
local notation "HY" => sourceKPAutomorphicCompactOrbitHeight K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPSelectedCuspBand_nonempty (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A < B) :
    (sourceKPSelectedCuspBand K hζ b A B).Nonempty := by
  let x : Xf := (1,b)
  let c : ℝ := 2 * (Fintype.card (InfinitePlace K) : ℝ)
  let L : ℝ := (A+B)/2
  let t : ℝ := Real.log (L/HF x)/c
  have hL : 0 < L := by dsimp only [L]; linarith
  have hH : 0 < HF x := sourceKPFiniteLevelHeight_pos K hζ x
  have hc : 0 < c := mul_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)
  let y := sourceKPFiniteLevelRadialFlow K hζ t x
  have hy : HF y = L := by
    rw [show y = sourceKPFiniteLevelRadialFlow K hζ t x from rfl,
      sourceKPFiniteLevelRadialFlow_height]
    change Real.exp (c*t)*HF x = L
    have ht : c*t = Real.log (L/HF x) := by
      dsimp only [t]
      field_simp [hc.ne']
    rw [ht,Real.exp_log (div_pos hL hH),div_mul_cancel₀ _ hH.ne']
  refine ⟨sourceKPFiniteLevelToCompact K hζ y,⟨y,?_,rfl⟩⟩
  change A < HF y ∧ HF y < B ∧ y.2 ∈
    Set.range (fun γ : sourceKPRationalBorel K => γ.val • b)
  rw [hy]
  refine ⟨by dsimp only [L]; linarith,by dsimp only [L]; linarith,⟨1,?_⟩⟩
  change (1 : PGL(2,K)) • b = b
  exact one_smul _ _

theorem sourceKPSelectedCuspBand_measure_pos (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A < B) : 0 < μY (sourceKPSelectedCuspBand K hζ b A B) := by
  let : Measure.IsOpenPosMeasure μY := sourceKPAutomorphicCompactHaar_openPositive K hζ
  exact (sourceKPSelectedCuspBand_isOpen K hζ b A B).measure_pos μY
    (sourceKPSelectedCuspBand_nonempty K hζ b hA hAB)

theorem sourceKPFiniteUpper_eq_rational_on_fiber (q : SourceKPAdelicProjective K hζ)
    (t : 𝔸ᶠ[K]) :
    ∃ a : K, sourceKPFiniteAdeleUpperLift K hζ t • (sourceKPFiniteLevelMk K hζ q).2 =
      sourcePGL2Upper a • (sourceKPFiniteLevelMk K hζ q).2 := by
  obtain ⟨d,hd,hperiod⟩ := sourceKPAdelicCuspFiniteLevelPeriod K hζ q
  obtain ⟨a,ha⟩ := sourceKPCuspFiniteIdeal_remainder K d hd t
  obtain ⟨k,hk⟩ := hperiod (t-algebraMap K 𝔸ᶠ[K] a) ha
  let z := sourceKPAdelicUpperLift K hζ
    (sourceKPFiniteAddEmbedding K (t-algebraMap K 𝔸ᶠ[K] a))
  change q⁻¹*z*q = sourceKPFiniteDeepCoverLift K hζ k at hk
  have he : q * sourceKPFiniteDeepCoverLift K hζ k = z*q := by
    rw [← hk]
    group
  have hf := congrArg Prod.snd ((sourceKPFiniteLevelMk_eq_iff K hζ q (z*q)).mpr ⟨k,he⟩)
  have hfix : sourceKPFiniteAdeleUpperLift K hζ (t-algebraMap K 𝔸ᶠ[K] a) •
      (sourceKPFiniteLevelMk K hζ q).2 = (sourceKPFiniteLevelMk K hζ q).2 := hf.symm
  refine ⟨a,?_⟩
  calc
    _ = sourceKPFiniteAdeleUpperLift K hζ
        (algebraMap K 𝔸ᶠ[K] a+(t-algebraMap K 𝔸ᶠ[K] a)) •
        (sourceKPFiniteLevelMk K hζ q).2 := by congr 1; abel
    _ = _ := by
      rw [sourceKPFiniteAdeleUpperLift_add,mul_smul,hfix,sourceKPFiniteAdeleUpperLift_rational]
      rfl

theorem sourceKPSelectedCuspBand_upper_mem_iff (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) (q : SourceKPAdelicProjective K hζ) (hq : 1 < HC q) (t : 𝔸[K]) :
    sourceKPFiniteLevelToCompact K hζ
        (sourceKPFiniteLevelMk K hζ (sourceKPAdelicUpperLift K hζ t*q)) ∈
        sourceKPSelectedCuspBand K hζ b A B ↔
      sourceKPFiniteLevelToCompact K hζ (sourceKPFiniteLevelMk K hζ q) ∈
        sourceKPSelectedCuspBand K hζ b A B := by
  have hh := sourceKPAdelicCoverHeight_left_upper K hζ t q
  have ht : 1 < HC (sourceKPAdelicUpperLift K hζ t*q) := by rwa [hh]
  rw [sourceKPSelectedCuspBand_mem_iff K hζ b hA _ ht,
    sourceKPSelectedCuspBand_mem_iff K hζ b hA q hq,hh]
  obtain ⟨a,ha⟩ := sourceKPFiniteUpper_eq_rational_on_fiber K hζ q t.2
  have he : (sourceKPFiniteLevelMk K hζ (sourceKPAdelicUpperLift K hζ t*q)).2 =
      sourcePGL2Upper a • (sourceKPFiniteLevelMk K hζ q).2 := ha
  rw [he]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  let n : sourceKPRationalBorel K := ⟨sourcePGL2Upper a,sourceKPRationalBorel_upper K a⟩
  change n.val • (sourceKPFiniteLevelMk K hζ q).2 ∈
      Set.range (fun γ : sourceKPRationalBorel K => γ.val • b) ↔ _
  constructor
  · rintro ⟨γ,hγ⟩
    change γ.val • b = n.val • (sourceKPFiniteLevelMk K hζ q).2 at hγ
    refine ⟨n⁻¹*γ,?_⟩
    change (n.val⁻¹*γ.val) • b = _
    rw [mul_smul,hγ,inv_smul_smul]
  · rintro ⟨γ,hγ⟩
    change γ.val • b = (sourceKPFiniteLevelMk K hζ q).2 at hγ
    refine ⟨n*γ,?_⟩
    change (n.val*γ.val) • b = _
    rw [mul_smul,hγ]

def sourceKPSelectedCuspWeight (b : SourceKPFiniteLevelFiber K hζ) (A B : ℝ) : Y → ℂ :=
  (sourceKPSelectedCuspBand K hζ b A B).indicator 1

theorem sourceKPSelectedCuspWeight_measurable (b : SourceKPFiniteLevelFiber K hζ) (A B : ℝ) :
    Measurable (sourceKPSelectedCuspWeight K hζ b A B) :=
  measurable_const.indicator (sourceKPSelectedCuspBand_isOpen K hζ b A B).measurableSet

theorem sourceKPSelectedCuspWeight_norm_le (b : SourceKPFiniteLevelFiber K hζ) (A B : ℝ) (x : Y) :
    ‖sourceKPSelectedCuspWeight K hζ b A B x‖ ≤ 1 := by
  unfold sourceKPSelectedCuspWeight
  by_cases hx : x ∈ sourceKPSelectedCuspBand K hζ b A B <;> simp [hx]

theorem sourceKPSelectedCuspWeight_support (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ} (hA : 1 ≤ A) :
    Function.support (sourceKPSelectedCuspWeight K hζ b A B) ⊆ {x : Y | A < HY x ∧ HY x ≤ B} := by
  intro x hx
  have hm : x ∈ sourceKPSelectedCuspBand K hζ b A B := by
    by_contra hn
    exact hx (Set.indicator_of_notMem hn _)
  have hh := sourceKPSelectedCuspBand_height K hζ b hA hm
  exact ⟨hh.1,hh.2.le⟩

theorem sourceKPSelectedCuspWeight_upper (b : SourceKPFiniteLevelFiber K hζ) {A B : ℝ}
    (hA : 1 ≤ A) (q : SourceKPAdelicProjective K hζ) (hq : A < HC q) (t : 𝔸[K]) :
    sourceKPSelectedCuspWeight K hζ b A B
      (sourceKPFiniteLevelToCompact K hζ (sourceKPFiniteLevelMk K hζ
        (sourceKPAdelicUpperLift K hζ t*q))) =
    sourceKPSelectedCuspWeight K hζ b A B
      (sourceKPFiniteLevelToCompact K hζ (sourceKPFiniteLevelMk K hζ q)) := by
  have hm := sourceKPSelectedCuspBand_upper_mem_iff K hζ b (B := B) hA q (hA.trans_lt hq) t
  by_cases h : sourceKPFiniteLevelToCompact K hζ (sourceKPFiniteLevelMk K hζ q) ∈
      sourceKPSelectedCuspBand K hζ b A B
  · rw [sourceKPSelectedCuspWeight,Set.indicator_of_mem (hm.mpr h),Set.indicator_of_mem h]
    rfl
  · rw [sourceKPSelectedCuspWeight,Set.indicator_of_notMem (fun hn => h (hm.mp hn)),
      Set.indicator_of_notMem h]

end
end ArtinMatthews
