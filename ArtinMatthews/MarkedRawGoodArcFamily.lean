module

public import ArtinMatthews.MarkedRawGoodArcAgreement
public import ArtinMatthews.MarkedRootLiftedArcs


set_option backward.privateInPublic true
@[expose] public section

/-! The full literal first/beta arc family, including every fresh tuple
and every trial pair. Threshold averaging creates no extra endpoints. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev MarkedRawFirstArcIndex {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ) :=
  (markedRawDyadicOmissions a d₀) × ↥(Finset.Icc 1 ⌊Y^(1/5:ℝ)⌋₊)

abbrev MarkedRawBetaArcIndex {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) :=
  Σ p : Finset J × J,
    MarkedFreshPrimeTuple (fun k : ↥(Finset.univ \ p.1) => e k.1) x ×
      (↥(markedRawDirtyFullTrials e x a (p.1.erase p.2)) × ↥(markedRawDirtyFullTrials e x a (p.1.erase p.2)))

abbrev MarkedRawGoodArcIndex {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ) :=
  MarkedRawFirstArcIndex a d₀ Y ⊕ MarkedRawBetaArcIndex e x a

def markedRawGoodArcFrequency {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ) :
    MarkedRawGoodArcIndex e x a d₀ Y → ℤ
  | Sum.inl p => ((markedSourceCopiedProduct (markedRawNumericActive a) p.1.1*p.2.1:ℕ):ℤ)
  | Sum.inr p => (p.2.2.1.1-p.2.2.2.1)*markedFreshIntegerProduct
      (fun k : ↥(Finset.univ \ p.1.1) => e k.1) x p.2.1

def markedRawGoodArcWidth {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y : ℝ) :
    MarkedRawGoodArcIndex e x a d₀ Y → ℝ
  | Sum.inl _ => Y^(-7/10:ℝ)
  | Sum.inr p => 100*Real.exp (-((Real.log x)^(e p.1.2)))

def markedRawGoodArcLevels {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y R : ℝ) : Finset ℝ :=
  Finset.univ.biUnion (fun i : MarkedRawGoodArcIndex e x a d₀ Y =>
    markedRootLiftedArcLevels (markedRawGoodArcFrequency e x a d₀ Y i) R
      (markedRawGoodArcWidth e x a d₀ Y i))

theorem markedRawGoodArcLevels_subset {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y R : ℝ)
    (i : MarkedRawGoodArcIndex e x a d₀ Y) :
    markedRootLiftedArcLevels (markedRawGoodArcFrequency e x a d₀ Y i) R
      (markedRawGoodArcWidth e x a d₀ Y i) ⊆ markedRawGoodArcLevels e x a d₀ Y R := by
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hc⟩

theorem markedTransportedRatioAllCuts_mono (z w : Fin 2 → ℝ) {A B : Finset ℝ} (h : A ⊆ B) :
    markedTransportedRatioAllCuts z w A ⊆ markedTransportedRatioAllCuts z w B := by
  intro r hr
  rcases Finset.mem_insert.mp hr with hr | hr
  · exact Finset.mem_insert.mpr (Or.inl hr)
  · obtain ⟨a,ha,har⟩ := Finset.mem_image.mp hr
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,h ha,har⟩)

theorem markedRawCircleGood_transport_constancy {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y R : ℝ)
    (z w : Fin 2 → ℝ) (hdet : markedVectorDet z w = 1) {r s : ℝ}
    (hR : 0 ≤ R) (hfirst : Y^(-7/10:ℝ) ≤ 1)
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) ≤ 1)
    (hr : |markedTransportedRatio r z w| ≤ R) (hs : |markedTransportedRatio s z w| ≤ R)
    (hcut : ∀ t ∈ Set.uIcc r s,t ∉ markedTransportedRatioAllCuts z w (markedRawGoodArcLevels e x a d₀ Y R)) :
    MarkedRawCircleGood e x a d₀ Y (markedTransportedRatio r z w:AddCircle (1:ℝ)) ↔
      MarkedRawCircleGood e x a d₀ Y (markedTransportedRatio s z w:AddCircle (1:ℝ)) := by
  apply markedRawCircleGood_congr_arcs
  have hi (i : MarkedRawGoodArcIndex e x a d₀ Y) :
      ((markedTransportedRatio r z w:AddCircle (1:ℝ)) ∈
        markedBadRootMultiple (markedRawGoodArcFrequency e x a d₀ Y i) (markedRawGoodArcWidth e x a d₀ Y i)) ↔
      ((markedTransportedRatio s z w:AddCircle (1:ℝ)) ∈
        markedBadRootMultiple (markedRawGoodArcFrequency e x a d₀ Y i) (markedRawGoodArcWidth e x a d₀ Y i)) := by
    have hwidth : markedRawGoodArcWidth e x a d₀ Y i ≤ 1 := by
      cases i with
      | inl p => exact hfirst
      | inr p => exact hbeta p.1.2
    exact markedTransportedArc_iff_off_cuts z w hdet _ hR hwidth hr hs (fun t ht hm =>
      hcut t ht (markedTransportedRatioAllCuts_mono z w (markedRawGoodArcLevels_subset e x a d₀ Y R i) hm))
  constructor
  · intro o l hl
    exact hi (Sum.inl (o,⟨l,hl⟩))
  · intro I j t u v
    exact hi (Sum.inr ⟨(I,j),t,u,v⟩)

end ArtinMatthews
