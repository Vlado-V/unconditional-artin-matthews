module

public import ArtinMatthews.SourceKPReflectionHorizontal


set_option backward.privateInPublic true
@[expose] public section

/-! Products of the distinct horizontal derivatives commute with the
signed Weyl coordinate reflection, with their literal product phase. -/
namespace ArtinMatthews
open NumberField SourceArchJacquet SourceHyperbolicGreen OAI.CubicEisenstein Filter
open scoped NumberField MatrixGroups AdeleRing Classical Topology ContDiff LineDeriv
noncomputable section

variable {ι : Type*} [Fintype ι]

def sourceProductHorizontalList (ε : ι → Bool) (l : List ι) (F : ProductSpace ι → ℂ) :
    ProductSpace ι → ℂ :=
  l.foldr (fun v G => sourceProductHorizontal (ε v) v G) F

private theorem horizontal_contDiffAt (ε : Bool) (v : ι)
    {F : ProductSpace ι → ℂ} {p : ProductSpace ι} (hF : ContDiffAt ℝ (∞ : ℕ∞ω) F p) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceProductHorizontal ε v F) p := by
  have hD : ContDiffAt ℝ (∞ : ℕ∞ω) (fderiv ℝ F) p := hF.fderiv_right (by simp)
  have hX := hD.clm_apply (contDiffAt_const (c := productDirection v 0))
  have hY := hD.clm_apply (contDiffAt_const (c := productDirection v 1))
  have hH : ContDiffAt ℝ (∞ : ℕ∞ω) (fun q : ProductSpace ι => (q v 2 : ℂ)) p :=
    (productHeightCLM v).contDiff.contDiffAt
  have h := hH.mul (hX.add ((contDiffAt_const (c := sourceHorizontalOrientation ε)).mul hY))
  exact h.div_const 2

theorem sourceProductHorizontalList_contDiffAt (ε : ι → Bool) (l : List ι)
    {F : ProductSpace ι → ℂ} {p : ProductSpace ι} (hF : ContDiffAt ℝ (∞ : ℕ∞ω) F p) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceProductHorizontalList ε l F) p := by
  induction l with
  | nil => exact hF
  | cons v l ih => exact horizontal_contDiffAt (ε v) v ih

theorem sourceProductHorizontalList_congrOn (ε : ι → Bool) (l : List ι)
    {F G : ProductSpace ι → ℂ} (h : Set.EqOn F G (productUpper ι)) :
    Set.EqOn (sourceProductHorizontalList ε l F) (sourceProductHorizontalList ε l G)
      (productUpper ι) := by
  induction l with
  | nil => exact h
  | cons v l ih =>
    intro p hp
    have he : sourceProductHorizontalList ε l F =ᶠ[𝓝 p] sourceProductHorizontalList ε l G :=
      Filter.Eventually.mono ((productUpper_isOpen ι).mem_nhds hp) ih
    change sourceProductHorizontal (ε v) v (sourceProductHorizontalList ε l F) p =
      sourceProductHorizontal (ε v) v (sourceProductHorizontalList ε l G) p
    simp only [sourceProductHorizontal,productPartial,he.fderiv_eq]

private theorem horizontal_eq_const_mul_of_lines (ε : Bool) (v : ι) (C : ℂ)
    {F G : ProductSpace ι → ℂ} {p : ProductSpace ι}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p)
    (he : ∀ j : Fin 3, (fun t : ℝ => F (p + t • productDirection v j)) =ᶠ[𝓝 0]
      (fun t : ℝ => C * G (p + t • productDirection v j))) :
    sourceProductHorizontal ε v F p = C * sourceProductHorizontal ε v G p := by
  have hh (j : Fin 3) : productPartial F v j p = C * productPartial G v j p := by
    have h₁ : HasDerivAt (fun t : ℝ => F (p + t • productDirection v j)) (productPartial F v j p) 0 :=
      hF.hasFDerivAt.hasLineDerivAt (productDirection v j)
    have h₂ : HasDerivAt (fun t : ℝ => G (p + t • productDirection v j)) (productPartial G v j p) 0 :=
      hG.hasFDerivAt.hasLineDerivAt (productDirection v j)
    exact h₁.unique ((h₂.const_mul C).congr_of_eventuallyEq (he j))
  simp only [sourceProductHorizontal,hh]
  ring

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "Ω" => productUpper V
local notation "A" => sourceKPReflectionArch K hζ

theorem sourceKPReflectionHorizontalList_comp (b : Kˣ) (ε : V → Bool) (l : List V)
    (hl : l.Nodup) (F : X → ℂ) (hF : ∀ p ∈ Ω, ContDiffAt ℝ (∞ : ℕ∞ω) F p)
    (p : X) (hp : p ∈ Ω) (haxis : ∀ v ∈ l, p v 0 = 0 ∧ p v 1 = 0) :
    sourceProductHorizontalList ε l (F ∘ A b) p =
      (l.map (fun v => sourceKPReflectionHorizontalPhase K hζ b (ε v) v)).prod *
        sourceProductHorizontalList (fun v => !(ε v)) l F (A b p) := by
  induction l generalizing p with
  | nil => simp [sourceProductHorizontalList]
  | cons v l ih =>
    have hN := List.nodup_cons.mp hl
    let G := sourceProductHorizontalList (fun v => !(ε v)) l F
    let H := sourceProductHorizontalList ε l (F ∘ A b)
    let C := (l.map (fun v => sourceKPReflectionHorizontalPhase K hζ b (ε v) v)).prod
    have hA (q : X) (hq : q ∈ Ω) : ContDiffAt ℝ (∞ : ℕ∞ω) (A b) q :=
      sourceKPArchEuclideanAction_contDiffAt K hζ _ q hq
    have hAu (q : X) : A b q ∈ Ω := sourceKPArchEuclideanAction_positive K hζ _ q
    have hG : ContDiffAt ℝ (∞ : ℕ∞ω) G (A b p) :=
      sourceProductHorizontalList_contDiffAt _ _ (hF _ (hAu p))
    have hH : ContDiffAt ℝ (∞ : ℕ∞ω) H p :=
      sourceProductHorizontalList_contDiffAt _ _ ((hF _ (hAu p)).comp p (hA p hp))
    have hline (j : Fin 3) :
        (fun t : ℝ => H (p + t • productDirection v j)) =ᶠ[𝓝 0]
          (fun t : ℝ => C * (G ∘ A b) (p + t • productDirection v j)) := by
      let L := fun t : ℝ => p + t • productDirection v j
      have hL : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
      have h0 : L 0 = p := by simp [L]
      have hnear : ∀ᶠ t in 𝓝 0, L t ∈ Ω :=
        hL.continuousAt.preimage_mem_nhds ((productUpper_isOpen V).mem_nhds (h0 ▸ hp))
      filter_upwards [hnear] with t ht
      apply ih hN.2 (L t) ht
      intro k hk
      have hkv : k ≠ v := fun h => hN.1 (h ▸ hk)
      have he : L t k = p k := by
        change p k + t • ((Pi.single v (euclideanCoordinateVector j) : X) k) = p k
        rw [Pi.single_eq_of_ne hkv,smul_zero,add_zero]
      rw [he]
      exact haxis k (List.mem_cons_of_mem _ hk)
    have hcomp := horizontal_eq_const_mul_of_lines (ε v) v C
      (hH.differentiableAt (by simp)) ((hG.comp p (hA p hp)).differentiableAt (by simp)) hline
    have hax := haxis v (List.mem_cons_self ..)
    change sourceProductHorizontal (ε v) v H p =
      (sourceKPReflectionHorizontalPhase K hζ b (ε v) v * C) *
        sourceProductHorizontal (!(ε v)) v G (A b p)
    rw [hcomp,sourceKPReflectionHorizontal_comp K hζ b (ε v) v G p hp hax.1 hax.2
      (hG.differentiableAt (by simp))]
    ring

theorem sourceKPReflectionHorizontalList_quotient (b : Kˣ) (ε : V → Bool)
    (l : List V) (hl : l.Nodup) (qf : SourceKPFiniteLevelFiber K hζ)
    (W : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (hW : ContDiffOn ℝ (∞ : ℕ∞ω) (sourceKPCompactChartPullback K hζ W (sourceKPReflectionWeyl K b • qf)) Ω)
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceProductHorizontalList ε l (sourceKPCompactChartPullback K hζ W qf)
        (sourceKPCuspHeightPoint K y) =
      (l.map (fun v => sourceKPReflectionHorizontalPhase K hζ b (ε v) v)).prod *
        sourceProductHorizontalList (fun v => !(ε v)) l
          (sourceKPCompactChartPullback K hζ W (sourceKPReflectionWeyl K b • qf))
          (sourceKPCuspHeightPoint K (sourceKPReflectionHeight K hζ b y)) := by
  let F := sourceKPCompactChartPullback K hζ W (sourceKPReflectionWeyl K b • qf)
  let p := sourceKPCuspHeightPoint K y
  have hp : p ∈ Ω := fun v _ => hy v
  have he : Set.EqOn (sourceKPCompactChartPullback K hζ W qf) (F ∘ A b) Ω :=
    fun q hq => sourceKPReflectionWeyl_pullback K hζ b qf W q hq
  rw [sourceProductHorizontalList_congrOn ε l he hp]
  have h := sourceKPReflectionHorizontalList_comp K hζ b ε l hl F
    (fun q hq => (hW q hq).contDiffAt ((productUpper_isOpen V).mem_nhds hq))
    p hp (fun _ _ => ⟨rfl,rfl⟩)
  rw [sourceKPReflectionArch_heightPoint K hζ b y hy] at h
  exact h

end
end ArtinMatthews
