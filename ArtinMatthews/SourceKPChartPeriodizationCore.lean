module

public import ArtinMatthews.SourceKPChartPeriodization


set_option backward.privateInPublic true
@[expose] public section

/-! Compact tests descend through the actual arithmetic periodization. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ

theorem sourceKPChartPeriodizationComponent_range (b : SourceKPFiniteLevelFiber K hζ) :
    Set.range (sourceKPUpperToCompact K hζ b) =
      (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {sourceKPFiniteOrbitMk K hζ b} := by
  ext y
  constructor
  · rintro ⟨p,rfl⟩
    exact (sourceKPArithmeticUpperComponentHomeomorph K hζ b (Quotient.mk _ p)).prop
  · intro hy
    obtain ⟨q,hq⟩ := (sourceKPArithmeticUpperComponentHomeomorph K hζ b).surjective ⟨y,hy⟩
    induction q using Quotient.inductionOn with
    | _ p => exact ⟨p,congrArg Subtype.val hq⟩

theorem sourceKPChartPeriodizationComponent_closed (b : SourceKPFiniteLevelFiber K hζ) :
    IsClosed (Set.range (sourceKPUpperToCompact K hζ b)) := by
  rw [sourceKPChartPeriodizationComponent_range]
  exact (isClosed_discrete _).preimage (sourceKPAutomorphicCompactFiniteOrbit_continuous K hζ)

def sourceKPChartPeriodizationGlobal (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) (y : Y) : ℂ :=
  if hy : y ∈ Set.range (sourceKPUpperToCompact K hζ b) then
    sourceKPChartPeriodization K hζ b φ hy.choose else 0

theorem sourceKPChartPeriodizationGlobal_apply (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPChartPeriodizationGlobal K hζ b φ (sourceKPUpperToCompact K hζ b p) =
      sourceKPChartPeriodization K hζ b φ p := by
  have hp : sourceKPUpperToCompact K hζ b p ∈ Set.range (sourceKPUpperToCompact K hζ b) :=
    Set.mem_range_self p
  rw [sourceKPChartPeriodizationGlobal,dite_eq_left hp]
  obtain ⟨γ,hγ,ha⟩ := (sourceKPUpperToCompact_eq_iff_rational K hζ b b hp.choose p).mp hp.choose_spec
  let δ : sourceKPArchComponentSubgroup K hζ b :=
    ⟨sourceKPRationalArchMap K hζ γ,⟨γ,hγ,rfl⟩⟩
  rw [← ha]
  exact sourceKPChartPeriodization_smul K hζ b φ δ p

theorem sourceKPChartPeriodizationGlobal_off (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) (y : Y)
    (hy : y ∉ Set.range (sourceKPUpperToCompact K hζ b)) :
    sourceKPChartPeriodizationGlobal K hζ b φ y = 0 := by
  rw [sourceKPChartPeriodizationGlobal,dite_eq_right hy]

theorem sourceKPChartPeriodizationGlobal_continuous (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) : Continuous (sourceKPChartPeriodizationGlobal K hζ b φ) := by
  apply continuous_def.mpr
  intro V hV
  let P := sourceKPUpperToCompact K hζ b
  let R := Set.range P
  let U := P '' (sourceKPChartPeriodization K hζ b φ ⁻¹' V)
  let W : Set Y := if (0 : ℂ) ∈ V then Rᶜ else ∅
  have hU : IsOpen U := (sourceKPUpperToCompact_isOpenMap K hζ b) _
    (hV.preimage (sourceKPChartPeriodization_continuous K hζ b φ))
  have hW : IsOpen W := by
    unfold W
    split_ifs
    · exact (sourceKPChartPeriodizationComponent_closed K hζ b).isOpen_compl
    · exact isOpen_empty
  have he : sourceKPChartPeriodizationGlobal K hζ b φ ⁻¹' V = U ∪ W := by
    ext y
    constructor
    · intro hy
      by_cases hr : y ∈ R
      · obtain ⟨p,rfl⟩ := hr
        change sourceKPChartPeriodizationGlobal K hζ b φ (sourceKPUpperToCompact K hζ b p) ∈ V at hy
        rw [sourceKPChartPeriodizationGlobal_apply] at hy
        exact Or.inl ⟨p,hy,rfl⟩
      · have h0 : (0 : ℂ) ∈ V := by
          simpa only [Set.mem_preimage,sourceKPChartPeriodizationGlobal_off K hζ b φ y hr] using hy
        exact Or.inr (by simpa only [W,ite_eq_left h0,Set.mem_compl_iff] using hr)
    · rintro (⟨p,hp,rfl⟩|hy)
      · change sourceKPChartPeriodizationGlobal K hζ b φ (sourceKPUpperToCompact K hζ b p) ∈ V
        rw [sourceKPChartPeriodizationGlobal_apply]
        exact hp
      · by_cases h0 : (0 : ℂ) ∈ V
        · have hr : y ∉ R := by simpa only [W,ite_eq_left h0,Set.mem_compl_iff] using hy
          simpa only [Set.mem_preimage,sourceKPChartPeriodizationGlobal_off K hζ b φ y hr] using h0
        · simp only [W,ite_eq_right h0,Set.mem_empty_iff_false] at hy
  rw [he]
  exact hU.union hW

theorem sourceKPChartPeriodizationGlobal_tsupport (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) : tsupport (sourceKPChartPeriodizationGlobal K hζ b φ) ⊆
      sourceKPUpperToCompact K hζ b '' sourceKPChartTestUpperSupport K φ := by
  have hc := (sourceKPChartTestUpperSupport_compact K φ).image (sourceKPUpperToCompact_continuous K hζ b)
  apply closure_minimal _ hc.isClosed
  intro y hy
  by_cases hr : y ∈ Set.range (sourceKPUpperToCompact K hζ b)
  · obtain ⟨p,rfl⟩ := hr
    have hp : sourceKPChartPeriodization K hζ b φ p ≠ 0 := by
      simpa only [Function.mem_support,sourceKPChartPeriodizationGlobal_apply] using hy
    have hsome : ∃ γ, sourceKPChartPeriodTerm K hζ b φ γ p ≠ 0 := by
      by_contra h
      have hz : ∀ γ, sourceKPChartPeriodTerm K hζ b φ γ p = 0 := by
        intro γ
        by_contra hn
        exact h ⟨γ,hn⟩
      exact hp (by simp [sourceKPChartPeriodization,hz])
    obtain ⟨γ,hγ⟩ := hsome
    exact ⟨γ⁻¹ • p,sourceKPChartTest_mem_upperSupport K φ _ hγ,
      sourceKPUpperToCompact_smul K hζ b γ⁻¹ p⟩
  · exact False.elim (hy (sourceKPChartPeriodizationGlobal_off K hζ b φ y hr))

theorem sourceKPChartPeriodizationGlobal_hasCompactSupport (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) : HasCompactSupport (sourceKPChartPeriodizationGlobal K hζ b φ) :=
  ((sourceKPChartTestUpperSupport_compact K φ).image (sourceKPUpperToCompact_continuous K hζ b)).of_isClosed_subset
    isClosed_closure (sourceKPChartPeriodizationGlobal_tsupport K hζ b φ)

theorem sourceKPChartPeriodizationGlobal_pullback_contDiffOn (b c : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) :
    ContDiffOn ℝ 2 (sourceKPCompactChartPullback K hζ (sourceKPChartPeriodizationGlobal K hζ b φ) c)
      (productUpper (InfinitePlace K)) := by
  by_cases h : ∃ γ : PGL(2, K), γ • c = b
  · obtain ⟨γ,hγ⟩ := h
    let a := sourceKPRationalArchMap K hζ γ
    have ha : ContDiffOn ℝ 2 (sourceKPArchEuclideanAction K hζ a) (productUpper (InfinitePlace K)) :=
      fun x hx => ((sourceKPArchEuclideanAction_contDiffAt K hζ a x hx).of_le (by simp)).contDiffWithinAt
    have hc := (sourceKPChartPeriodization_contDiffOn K hζ b φ).comp ha
      (fun x _ => sourceKPArchEuclideanAction_positive K hζ a x)
    apply hc.congr
    intro x hx
    rw [sourceKPCompactChartPullback,ite_eq_left hx]
    have he : sourceKPUpperToCompact K hζ b
        (sourceKPArchUpperAction K hζ a (sourceKPArchEuclideanUpperMap K x)) =
          sourceKPUpperToCompact K hζ c (sourceKPArchEuclideanUpperMap K x) := by
      simpa only [hγ] using sourceKPUpperToCompact_rational K hζ γ c (sourceKPArchEuclideanUpperMap K x)
    rw [← he,sourceKPChartPeriodizationGlobal_apply]
    change sourceKPChartPeriodization K hζ b φ
        (sourceKPArchUpperAction K hζ a (sourceKPArchEuclideanUpperMap K x)) =
      sourceKPChartPeriodization K hζ b φ (sourceKPArchEuclideanUpperMap K (sourceKPArchEuclideanAction K hζ a x))
    rw [sourceKPArchEuclideanAction,sourceKPArchUpperEuclideanMap_left_inverse]
  · have hz : ContDiffOn ℝ 2 (fun _ : ProductSpace (InfinitePlace K) => (0 : ℂ))
        (productUpper (InfinitePlace K)) := contDiffOn_const
    apply hz.congr
    intro x hx
    rw [sourceKPCompactChartPullback,ite_eq_left hx]
    apply sourceKPChartPeriodizationGlobal_off
    rintro ⟨p,hp⟩
    obtain ⟨γ,hγ,_⟩ := (sourceKPUpperToCompact_eq_iff_rational K hζ b c p _).mp hp
    exact h ⟨γ,hγ⟩

def sourceKPChartPeriodizationCore (b : SourceKPFiniteLevelFiber K hζ)
    (φ : h1Tests (InfinitePlace K) 2) : sourceKPCompactC2Core K hζ :=
  ⟨sourceKPChartPeriodizationGlobal K hζ b φ,sourceKPChartPeriodizationGlobal_continuous K hζ b φ,
    sourceKPChartPeriodizationGlobal_hasCompactSupport K hζ b φ,
    fun c => sourceKPChartPeriodizationGlobal_pullback_contDiffOn K hζ b c φ⟩

end
end ArtinMatthews
