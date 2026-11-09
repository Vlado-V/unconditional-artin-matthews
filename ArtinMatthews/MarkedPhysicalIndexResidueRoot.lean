module

public import ArtinMatthews.MarkedPhysicalIndexWeightedRoot
public import ArtinMatthews.MarkedPhysicalResidueMonomialBounds
public import ArtinMatthews.MarkedPhysicalPathBonferroni


set_option backward.privateInPublic true
@[expose] public section

/-! Actual performed-modulus root comparison for the pure coordinate
index. The coefficient is the original kernel times its literal active
incidence and Bonferroni monomial. All modulus and scalar bounds are
discharged from the actual labels and visit schedule. -/

noncomputable section
namespace ArtinMatthews
open Filter
attribute [local instance] Classical.propDecidable

def markedPhysicalCoordinateIndexResidueFactor {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex P M n R) (hR : 1≤R) (q : ℝ)
    (T : Finset ℕ) (hT : T⊆markedPhysicalBandPrimes P)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))) : ℝ :=
  if markedPhysicalResidueLabelValid (markedPhysicalBonferroniModulus_squarefree hP Finset.univ i.1 hT)
      g Finset.univ i.1 (markedPhysicalCoordinateIndexPath i.2.1)
        (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) then
    markedPhysicalResidueBonferroniMonomial (markedPhysicalBonferroniModulus_squarefree hP Finset.univ i.1 hT)
      g Finset.univ i.1 (markedMemoryVisitQ q n) (markedPhysicalCoordinateIndexPath i.2.1)
        (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) T
  else 0

theorem markedPhysicalCoordinateIndexResidueFactor_mem_unitInterval
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M n R : ℕ}
    (i : MarkedPhysicalCoordinateIndex P M n R) (hR : 1≤R) {q : ℝ} (hq0 : 0≤q) (hq1 : q≤1)
    (T : Finset ℕ) (hT : T⊆markedPhysicalBandPrimes P)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (markedPhysicalBonferroniModulus Finset.univ i.1 T))) :
    0 ≤ markedPhysicalCoordinateIndexResidueFactor hP i hR q T hT g ∧
      markedPhysicalCoordinateIndexResidueFactor hP i hR q T hT g ≤ 1 := by
  unfold markedPhysicalCoordinateIndexResidueFactor
  split_ifs
  · exact markedPhysicalResidueBonferroniMonomial_mem_unitInterval _ g Finset.univ i.1
      (markedMemoryVisitQ q n) (fun v _ => markedPhysicalVisitQ_mem_unitInterval hq0 hq1 n v)
      (markedPhysicalCoordinateIndexPath i.2.1) (markedPhysicalCoordinateIndexPath_primitive hR i.2.1) T
  · exact ⟨le_rfl,zero_le_one⟩

theorem markedPhysicalCoordinateIndex_selected_root_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) (heUpper : ∀ j,e j≤(1/5:ℝ))
    {δ : ℝ} (hδ : 0<δ) (B C G A : ℝ) (hB : 8≤B) (hG : 0≤G) (hA : 0≤A)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (Hη W v₀ : ℝ)
    (hHη : 0≤Hη) (hW : 0≤W) (hv0 : 0<v₀)
    (hη : ∀ t,‖η t‖≤Hη) (hψ : ∀ t,‖ψ t‖≤W) :
    ∀ᶠ x : ℝ in atTop,∀ (V : J → ℝ) (R : ℕ)
      (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x)
        (markedPadSlots x) (markedMemoryMomentLength x) R) (hR : 1≤R)
      (T : Finset ℕ)
      (hT : T⊆markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \ markedPhysicalPathUsedPrimes Finset.univ i.1)
      (_hcard : T.card≤2*markedPhysicalBonferroniDepth x+1),
      let S := markedPhysicalBonferroniModulus Finset.univ i.1 T
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U Vr d₀ Y Q q : ℝ),
      (∀ j,v₀≤V j) → x^δ≤U → x^δ≤Vr →
      Real.exp ((Real.log x)^(1/10:ℝ))≤Y → Y≤Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      (R:ℝ)+1≤Real.exp (B*(Real.log x)^(99/100:ℝ)) →
      1≤Q → Q≤(Real.log x)^A → 0≤q → q≤1 →
      let r := markedPhysicalCoordinateIndexResidueFactor (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1)
        i hR q T (fun _ hp => (Finset.mem_sdiff.mp (hT hp)).1) g
      let κ := (r:ℂ)*markedPhysicalCoordinateIndexCoefficient (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V ⌊(Real.log x)^(1/100:ℝ)⌋₊ ψ η d₀ Y Q i
      Real.exp (C*(Real.log x)^(99/100:ℝ))*
        (‖markedRootConstantIndicatorSum g U Vr (markedPhysicalCoordinateIndexGoodSet e x d₀ Y U Vr i hR) κ-
          (U*Vr/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))) •
            (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U Vr i hR • κ)‖/(U*Vr)) ≤
        (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedPhysicalCoordinateIndex_weighted_root_log_saving e he heUpper hδ
    (16*(Fintype.card J:ℝ)+10) B C G A hB hG hA ψ η Hη W v₀ hHη hW hv0 hη hψ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  intro V R i hR T hT hcard
  dsimp only
  intro g U Vr d₀ Y Q q hV hU hVr hY hYhi hRhi hQ hQhi hq0 hq1
  have hTP : T⊆markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) :=
    fun _ hp => (Finset.mem_sdiff.mp (hT hp)).1
  have hr := markedPhysicalCoordinateIndexResidueFactor_mem_unitInterval
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) i hR hq0 hq1 T hTP g
  exact hx V R i hR _ g U Vr d₀ Y Q _ hV hU hVr
    (markedPhysicalBonferroniModulus_squarefree (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) Finset.univ i.1 hTP)
    (markedPhysicalActualBonferroniModulus_bound e hlog heUpper i.1 T hT hcard)
    hY hYhi hRhi hQ hQhi hr.1 hr.2

end ArtinMatthews
