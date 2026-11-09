module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeTargetMap
public import ArtinMatthews.MarkedMinorArcDirtyPermutationAction
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetryBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! The literal second-good root test uses all source omissions and the
actual smaller-band prime choices. It is independent of pending indices. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawDirtyFullTrials {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (source : MarkedRawActive (markedRawActualPrimeBand e x) M) (I : Finset J) : Finset ℤ :=
  Finset.univ.image (fun c : (J → Fin M) × MarkedTrialPrimeChoices (fun j : I => e j.1) x =>
    ((markedSourceCopiedProduct (markedRawNumericActive source) c.1 * ∏ j : I,(c.2 j:ℕ):ℕ):ℤ))

/-- Every literal pending-index trial is one of the actual full prime-band
trials. There is no row/count hypothesis and no change to the fresh law. -/
theorem markedDirtyRawEdgeTrials_subset_full {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M B : ℕ}
    (source : MarkedRawActive (markedRawActualPrimeBand e x) M)
    (memory : MarkedRawMemory (markedRawActualPrimeBand e x) B) (I : Finset J) :
    markedDirtyRawEdgeTrials source memory I ⊆ markedRawDirtyFullTrials e x source I := by
  classical
  intro q hq
  obtain ⟨⟨o,z⟩,ho,hq⟩ := Finset.mem_image.mp hq
  obtain ⟨t,_,ht⟩ := Finset.mem_image.mp (Finset.mem_product.mp ho).2
  let p : MarkedTrialPrimeChoices (fun j : I => e j.1) x := fun j =>
    ⟨((memory.2 j.1 (t j)).1.1:ℕ),(mem_markedRawPrimeBand _ _).mp (memory.2 j.1 (t j)).1.2⟩
  apply Finset.mem_image.mpr
  refine ⟨(o,p),Finset.mem_univ _,?_⟩
  change ((markedSourceCopiedProduct (markedRawNumericActive source) o *
    markedRawPromotionTuplePrimeProduct memory I t:ℕ):ℤ)=q
  rw [ht]
  exact hq

theorem markedRawDirtyFullTrials_slots {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (σ : J → Equiv.Perm (Fin M)) (I : Finset J) :
    markedRawDirtyFullTrials e x (markedRawSlotEquiv σ s).2.1 I =
      markedRawDirtyFullTrials e x s.2.1 I := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨⟨o,p⟩,_,hq⟩ := Finset.mem_image.mp hq
    apply Finset.mem_image.mpr
    refine ⟨((fun j => σ j (o j)),p),Finset.mem_univ _,?_⟩
    change ((markedSourceCopiedProduct (fun j k => markedRawNumericActive s.2.1 j (σ j k)) o *
      ∏ j : I,(p j:ℕ):ℕ):ℤ)=q at hq
    rw [markedSourceCopiedProduct_permuted] at hq
    exact hq
  · intro hq
    obtain ⟨⟨o,p⟩,_,hq⟩ := Finset.mem_image.mp hq
    apply Finset.mem_image.mpr
    refine ⟨((fun j => (σ j).symm (o j)),p),Finset.mem_univ _,?_⟩
    change ((markedSourceCopiedProduct (fun j k => markedRawNumericActive s.2.1 j (σ j k))
      (fun j => (σ j).symm (o j)) * ∏ j : I,(p j:ℕ):ℕ):ℤ)=q
    rw [markedSourceCopiedProduct_permuted]
    simpa only [Equiv.apply_symm_apply] using hq

/-- The distinguished group is a maximal exponent among the promoted
groups. All other promoted bands are then smaller when e is injective. -/
def MarkedRawDirtySecondGood {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) : Prop :=
  ∀ (I : Finset J) (jstar : J), jstar ∈ I → (∀ j ∈ I,e j ≤ e jstar) →
    ((markedMinorIntegerTau r (w s.1)/markedMinorIntegerTau r s.1.1:ℝ):AddCircle (1:ℝ)) ∉
      {a | Real.exp (-((Real.log x)^(e jstar))/4) ≤
        markedPairFailureProbability (markedRawDirtyFullTrials e x s.2.1 (I.erase jstar))
          (markedFreshIntegerProduct (fun j : ↥(Finset.univ \ I) => e j.1) x)
          (markedFreshHarmonicLaw (fun j : ↥(Finset.univ \ I) => e j.1) x)
          (100*Real.exp (-((Real.log x)^(e jstar)))) a}

theorem markedRawDirtySecondGood_slots {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) (σ : J → Equiv.Perm (Fin M)) :
    MarkedRawDirtySecondGood e x r w (markedRawSlotEquiv σ s) ↔
      MarkedRawDirtySecondGood e x r w s := by
  simp only [MarkedRawDirtySecondGood,markedRawDirtyFullTrials_slots]
  rfl

def markedRawDirtySecondGoodCutoff {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) : ℂ :=
  if MarkedRawDirtySecondGood e x r w s then χ s else 0

def markedRawDirtyGoodCutoff {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ) :=
  markedRawFirstGoodCutoff r d₀ Y w (markedRawDirtySecondGoodCutoff e x r w χ)

theorem markedRawDirtySecondGoodCutoff_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    ‖markedRawDirtySecondGoodCutoff e x r w χ s‖ ≤ 1 := by
  classical
  unfold markedRawDirtySecondGoodCutoff
  split_ifs
  · exact hχ s
  · simp

theorem markedRawDirtyGoodCutoff_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ) (hχ : ∀ s,‖χ s‖ ≤ 1)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z) :
    ‖markedRawDirtyGoodCutoff e x r d₀ Y w χ s‖ ≤ 1 :=
  markedRawFirstGoodCutoff_norm_le r d₀ Y w _ (markedRawDirtySecondGoodCutoff_norm_le e x r w χ hχ) s

theorem markedRawDirtyGoodCutoff_eq_zero_of_not_second {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (hs : ¬MarkedRawDirtySecondGood e x r w s) :
    markedRawDirtyGoodCutoff e x r d₀ Y w χ s=0 := by
  classical
  simp only [markedRawDirtyGoodCutoff,markedRawFirstGoodCutoff,markedRawDirtySecondGoodCutoff,
    ite_eq_right hs,ite_self]

theorem markedRawDirtySecondGoodCutoff_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
    (hχ : ∀ z a,MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (z : Z) (a : MarkedRawActive (markedRawActualPrimeBand e x) M) :
    MarkedRawMemorySymmetric (fun m => markedRawDirtySecondGoodCutoff e x r w χ (z,(a,m))) := by
  classical
  intro m σ
  unfold markedRawDirtySecondGoodCutoff
  change (if MarkedRawDirtySecondGood e x r w (z,(a,m)) then χ (z,(a,markedRawMemoryPermute m σ)) else 0)=_
  have hh : χ (z,(a,markedRawMemoryPermute m σ))=χ (z,(a,m)) := hχ z a m σ
  rw [hh]

theorem markedRawDirtyGoodCutoff_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)} (w : Z → ℤ × ℤ)
    (χ : MarkedRawState (markedRawActualPrimeBand e x) M B Z → ℂ)
    (hχ : ∀ z a,MarkedRawMemorySymmetric (fun m => χ (z,(a,m))))
    (z : Z) (a : MarkedRawActive (markedRawActualPrimeBand e x) M) :
    MarkedRawMemorySymmetric (fun m => markedRawDirtyGoodCutoff e x r d₀ Y w χ (z,(a,m))) :=
  markedRawFirstGoodCutoff_symmetric r d₀ Y w _ (markedRawDirtySecondGoodCutoff_symmetric e x r w χ hχ) z a

end
end ArtinMatthews
